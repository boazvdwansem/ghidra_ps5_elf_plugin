package ps5.ghidra;

import ghidra.app.services.AnalyzerType;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.CodeUnit;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Program;
import ghidra.program.model.symbol.SourceType;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;
import ghidra.app.services.AbstractAnalyzer;
import ghidra.app.util.MemoryBlockUtils;
import ghidra.program.model.mem.MemoryBlock;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Ps5ElfAnalyzer extends AbstractAnalyzer {
    private static final int ET_SCE_EXEC_ASLR = 0xfe10;
    private static final int ET_SCE_DYNAMIC = 0xfe18;
    private static final int EM_X86_64 = 0x3e;
    private static final long PT_LOAD = 1;
    private static final long PT_DYNAMIC = 2;
    private static final long PT_SCE_PROCPARAM = 0x61000001L;
    private static final long PT_SCE_MODULE_PARAM = 0x61000002L;
    private static final long PT_GNU_EH_FRAME = 0x6474e550L;
    private static final long PT_SCE_COMMENT = 0x6fffff00L;
    private static final long PT_SCE_VERSION = 0x6fffff01L;
    private static final long DT_NULL = 0;
    private static final long DT_NEEDED = 1;
    private static final long DT_PLTGOT = 3;
    private static final long DT_HASH = 4;
    private static final long DT_RELA = 7;
    private static final long DT_RELASZ = 8;
    private static final long DT_RELAENT = 9;
    private static final long DT_SONAME = 14;
    private static final long DT_INIT = 12;
    private static final long DT_FINI = 13;
    private static final long DT_PLTREL = 20;
    private static final long DT_JMPREL = 23;
    private static final long DT_PLTRELSZ = 2;
    private static final long DT_STRTAB = 5;
    private static final long DT_SYMTAB = 6;
    private static final long DT_STRSZ = 10;
    private static final long DT_SYMENT = 11;
    private static final long DT_SCE_IDTABENTSZ = 0x60000005L;
    private static final long DT_SCE_MODULE_INFO = 0x6100000dL;
    private static final long DT_SCE_NEEDED_MODULE = 0x6100000fL;
    private static final long DT_SCE_MODULE_ATTR = 0x61000011L;
    private static final long DT_SCE_EXPORT_LIB = 0x61000013L;
    private static final long DT_SCE_IMPORT_LIB = 0x61000015L;
    private static final long DT_SCE_EXPORT_LIB_ATTR = 0x61000017L;
    private static final long DT_SCE_IMPORT_LIB_ATTR = 0x61000019L;
    private static final long DT_SCE_SYMTABSZ = 0x6100003fL;
    private static final long DT_SCE_ORIGINAL_FILENAME = 0x61000009L;
    private static final long DT_SCE_ORIGINAL_FILENAME_PPR = 0x61000041L;
    private static final long DT_SCE_MODULE_INFO_PPR = 0x61000043L;
    private static final long DT_SCE_NEEDED_MODULE_PPR = 0x61000045L;
    private static final long DT_SCE_IMPORT_LIB_PPR = 0x61000047L;
    private static final long DT_SCE_EXPORT_LIB_PPR = 0x61000049L;
    private static final String NID_ALPHABET =
            "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-";
    private static final long BAD = Long.MIN_VALUE;

    public Ps5ElfAnalyzer() {
        super("PS5 ELF Analyzer", "Decodes PS5 ELF metadata and NID symbols", AnalyzerType.BYTE_ANALYZER);
        setSupportsOneTimeAnalysis();
    }

    @Override
    public boolean canAnalyze(Program program) {
        try {
            Address base = program.getImageBase();
            if (program.getMemory().getByte(base) != 0x7f || program.getMemory().getByte(base.add(1)) != 'E' ||
                    program.getMemory().getByte(base.add(2)) != 'L' || program.getMemory().getByte(base.add(3)) != 'F') {
                return false;
            }
            return (program.getMemory().getByte(base.add(4)) & 0xff) == 2 &&
                    (program.getMemory().getByte(base.add(5)) & 0xff) == 1 &&
                    u16(program, base.add(18)) == EM_X86_64 &&
                    (u16(program, base.add(16)) == ET_SCE_EXEC_ASLR || u16(program, base.add(16)) == ET_SCE_DYNAMIC);
        }
        catch (Exception e) {
            return false;
        }
    }

    @Override
    public boolean getDefaultEnablement(Program program) {
        return canAnalyze(program);
    }

    @Override
    public boolean added(Program program, AddressSetView set, TaskMonitor monitor, MessageLog log)
            throws CancelledException {
        if (!canAnalyze(program)) {
            return false;
        }
        try {
            new Context(program, monitor, log).analyze();
            return true;
        }
        catch (Exception e) {
            log.appendMsg("PS5 ELF analyzer: " + e.getMessage());
            return false;
        }
    }

    private static int u16(Program program, Address address) throws Exception {
        return program.getMemory().getShort(address) & 0xffff;
    }

    private static final class Context {
        private final Program program;
        private final TaskMonitor monitor;
        private final MessageLog log;
        private final Map<Long, ObjectInfo> modules = new HashMap<>();
        private final Map<Long, ObjectInfo> libraries = new HashMap<>();
        private final Map<Long, String> knownNids = loadKnownNids();
        private final Set<Long> functions = new HashSet<>();
        private final List<SymbolInfo> symbols = new ArrayList<>();
        private long dynamicSize;
        private long strtabSize;
        private long rela;
        private long relaSize;
        private long relaEnt = 24;
        private long jmprel;
        private long jmprelSize;
        private long sonameOffset = -1;
        private long originalFilenameOffset = -1;
        private final List<Long> neededOffsets = new ArrayList<>();
        private long strtab;
        private long symtab;
        private long symtabSize;
        private long syment = 24;
        private String soname;
        private String originalFilename;

        Context(Program program, TaskMonitor monitor, MessageLog log) {
            this.program = program;
            this.monitor = monitor;
            this.log = log;
        }

        void analyze() throws Exception {
            Address base = program.getImageBase();
            long phoff = q64(base.add(32));
            int phentsize = u16(base.add(54));
            int phnum = u16(base.add(56));
            long dynamic = 0;
            for (int i = 0; i < phnum; i++) {
                Address ph = base.add(phoff + (long) i * phentsize);
                long type = u32(ph);
                long fileOffset = q64(ph.add(8));
                long vaddr = q64(ph.add(16));
                long filesz = q64(ph.add(32));
                long memsz = q64(ph.add(40));
                if (type == PT_DYNAMIC) dynamic = vaddr;
                if (type == PT_DYNAMIC) dynamicSize = memsz;
                if (type == PT_SCE_PROCPARAM || type == PT_SCE_MODULE_PARAM || type == PT_GNU_EH_FRAME ||
                        type == PT_SCE_COMMENT || type == PT_SCE_VERSION) {
                    ensureSpecialSegment(type, fileOffset, vaddr, filesz, memsz);
                    addComment(vaddr, "PS5 program header type 0x" + Long.toHexString(type));
                    if (type == PT_SCE_PROCPARAM) tryParseProcessParam(vaddr, filesz);
                    if (type == PT_SCE_MODULE_PARAM) tryParseModuleParam(vaddr, filesz);
                    if (type == PT_SCE_COMMENT) tryParseCommentSegment(vaddr, filesz);
                    if (type == PT_SCE_VERSION) tryParseVersionSegment(vaddr, filesz);
                    if (type == PT_GNU_EH_FRAME) tryParseEhFrameHeader(vaddr, filesz);
                }
            }
            if (dynamic == 0) return;
            parseDynamic(dynamic);
            resolveMetadata();
            if (strtab == 0 || symtab == 0 || syment < 24) return;
            int count = (int) (symtabSize / syment);
            for (int i = 0; i < count; i++) {
                monitor.checkCanceled();
                parseSymbol(symtab + i * syment);
            }
            applyRelocations(rela, relaSize, "RELA");
            applyRelocations(jmprel, jmprelSize, "JMPREL");
            if (soname != null) addComment(program.getImageBase(), "PS5 SONAME: " + soname);
            if (originalFilename != null) addComment(program.getImageBase(), "PS5 original filename: " + originalFilename);
        }

        private void ensureSpecialSegment(long type, long fileOffset, long vaddr, long filesz, long memsz) {
            if (filesz == 0 || program.getMemory().getBlock(address(vaddr)) != null) return;
            String name;
            if (type == PT_SCE_PROCPARAM) name = ".sce_process_param";
            else if (type == PT_SCE_MODULE_PARAM) name = ".sce_module_param";
            else if (type == PT_SCE_COMMENT) name = ".sce_comment";
            else if (type == PT_SCE_VERSION) name = ".sce_version";
            else name = ".eh_frame_hdr";
            String executablePath = program.getExecutablePath();
            if (executablePath == null || executablePath.isEmpty()) {
                log.appendMsg("PS5 ELF analyzer: no executable path for " + name);
                return;
            }
            try (InputStream stream = new FileInputStream(executablePath)) {
                long skipped = 0;
                while (skipped < fileOffset) {
                    long amount = stream.skip(fileOffset - skipped);
                    if (amount <= 0) throw new IOException("unable to seek to program-header data");
                    skipped += amount;
                }
                long length = Math.min(filesz, memsz == 0 ? filesz : memsz);
                MemoryBlock block = MemoryBlockUtils.createInitializedBlock(program, false, name,
                        address(vaddr), stream, length, "PS5 program header 0x" + Long.toHexString(type),
                        executablePath, false, false, type == PT_GNU_EH_FRAME, log, monitor);
                if (block != null && memsz > length) {
                    long bssSize = memsz - length;
                    program.getMemory().createUninitializedBlock(name + ".bss", address(vaddr + length), bssSize, false);
                }
            }
            catch (Exception e) {
                log.appendMsg("PS5 ELF analyzer: unable to create " + name + ": " + e.getMessage());
            }
        }

        private void parseDynamic(long address) throws Exception {
            long limit = dynamicSize > 0 ? dynamicSize / 16 : 0x10000;
            for (long i = 0; i < limit; i++) {
                Address entry = address(address + i * 16L);
                long tag = q64(entry);
                long value = q64(entry.add(8));
                if (tag == DT_NULL) return;
                switch ((int) tag) {
                    case (int) DT_STRTAB: strtab = value; break;
                    case (int) DT_SYMTAB: symtab = value; break;
                    case (int) DT_STRSZ: strtabSize = value; break;
                    case (int) DT_SYMENT: syment = value; break;
                    case (int) DT_SCE_SYMTABSZ: symtabSize = value; break;
                    case (int) DT_RELA: rela = value; break;
                    case (int) DT_RELASZ: relaSize = value; break;
                    case (int) DT_RELAENT: relaEnt = value; break;
                    case (int) DT_JMPREL: jmprel = value; break;
                    case (int) DT_PLTRELSZ: jmprelSize = value; break;
                    case (int) DT_PLTREL:
                        if (value != DT_RELA) log.appendMsg("PS5 ELF analyzer: unsupported PLT relocation format 0x" + Long.toHexString(value));
                        break;
                    case (int) DT_SCE_IDTABENTSZ:
                        if (value != 8) log.appendMsg("PS5 ELF analyzer: unsupported ID table entry size 0x" + Long.toHexString(value));
                        break;
                    case (int) DT_SONAME: sonameOffset = value; break;
                    case (int) DT_NEEDED: neededOffsets.add(value); break;
                    case (int) DT_SCE_ORIGINAL_FILENAME:
                    case (int) DT_SCE_ORIGINAL_FILENAME_PPR:
                        originalFilenameOffset = value; break;
                    case (int) DT_INIT: addComment(value, "PS5 init procedure"); break;
                    case (int) DT_FINI: addComment(value, "PS5 fini procedure"); break;
                    default: parseObjectTag(tag, value); break;
                }
            }
            log.appendMsg("PS5 ELF analyzer: dynamic table has no DT_NULL");
        }

        private void parseObjectTag(long tag, long value) throws Exception {
            boolean export = tag == DT_SCE_EXPORT_LIB || tag == DT_SCE_EXPORT_LIB_PPR || tag == DT_SCE_MODULE_INFO || tag == DT_SCE_MODULE_INFO_PPR;
            boolean info = export || tag == DT_SCE_IMPORT_LIB || tag == DT_SCE_IMPORT_LIB_PPR || tag == DT_SCE_NEEDED_MODULE || tag == DT_SCE_NEEDED_MODULE_PPR;
            boolean module = tag == DT_SCE_MODULE_INFO || tag == DT_SCE_MODULE_INFO_PPR || tag == DT_SCE_NEEDED_MODULE || tag == DT_SCE_NEEDED_MODULE_PPR || tag == DT_SCE_MODULE_ATTR;
            if (info) {
                long id = (value >>> 48) & 0xffff;
                Map<Long, ObjectInfo> target = module ? modules : libraries;
                ObjectInfo object = target.computeIfAbsent(id, ignored -> new ObjectInfo());
                object.export = export;
                object.nameOffset = value & 0xffffffffL;
                object.version = ((value >>> 32) & 0xff) + "." + ((value >>> 40) & 0xff);
            }
            if (tag == DT_SCE_MODULE_ATTR || tag == DT_SCE_EXPORT_LIB_ATTR || tag == DT_SCE_IMPORT_LIB_ATTR) {
                long id = (value >>> 48) & 0xffff;
                Map<Long, ObjectInfo> target = tag == DT_SCE_MODULE_ATTR ? modules : libraries;
                target.computeIfAbsent(id, ignored -> new ObjectInfo()).attributes = value & 0xffffffffffffL;
            }
        }

        private void resolveMetadata() throws Exception {
            if (strtab == 0) return;
            if (sonameOffset >= 0) soname = stringAt(strtab + sonameOffset);
            if (originalFilenameOffset >= 0) originalFilename = stringAt(strtab + originalFilenameOffset);
            for (long offset : neededOffsets) {
                addComment(program.getImageBase(), "PS5 needed module: " + stringAt(strtab + offset));
            }
            for (Map.Entry<Long, ObjectInfo> entry : modules.entrySet()) {
                ObjectInfo object = entry.getValue();
                if (object.nameOffset >= 0) object.name = stringAt(strtab + object.nameOffset);
                addComment(program.getImageBase(), "PS5 module " + entry.getKey() + ": " + object.describe());
            }
            for (Map.Entry<Long, ObjectInfo> entry : libraries.entrySet()) {
                ObjectInfo object = entry.getValue();
                if (object.nameOffset >= 0) object.name = stringAt(strtab + object.nameOffset);
                addComment(program.getImageBase(), "PS5 library " + entry.getKey() + ": " + object.describe());
            }
        }

        private void parseSymbol(long address) throws Exception {
            Address symbol = address(address);
            int nameOffset = (int) u32(symbol);
            int info = program.getMemory().getByte(symbol.add(4)) & 0xff;
            int shndx = u16(symbol.add(6));
            long value = q64(symbol.add(8));
            long size = q64(symbol.add(16));
            int type = info & 0xf;
            if ((type != 2 && type != 1) || nameOffset == 0) return;
            String encoded = stringAt(strtab + nameOffset);
            String name = decodeSymbolName(encoded, type);
            symbols.add(new SymbolInfo(name, encoded, value, size, shndx, type == 2));
            if (name == null || value == 0 || shndx == 0) return;
            label(value, name, "PS5 symbol: " + encoded);
            if (type == 2 && size > 0 && functions.add(value)) {
                FunctionManager manager = program.getFunctionManager();
                if (manager.getFunctionAt(address(value)) == null) {
                    manager.createFunction(name, address(value),
                            new AddressSet(address(value), address(value + size - 1)), SourceType.IMPORTED);
                }
            }
        }

        private String decodeSymbolName(String encoded, int type) {
            String[] parts = encoded.split("#", -1);
            if (parts.length != 3) return encoded;
            long nid = decode(parts[0]);
            long library = decodeObjectId(parts[1]);
            long module = decodeObjectId(parts[2]);
            ObjectInfo mod = modules.get(module);
            ObjectInfo lib = libraries.get(library);
            if (nid == BAD || mod == null || lib == null) return encoded;
            String result = knownNids.get(nid);
            if (result == null) result = String.format("nid%s_%s_%s_0x%016x", type == 2 ? "f" : "o", sanitize(mod.name), sanitize(lib.name), nid);
            return result;
        }

        private void applyRelocations(long table, long size, String kind) throws Exception {
            if (table == 0 || size == 0 || relaEnt < 24) return;
            for (long offset = 0; offset + relaEnt <= size; offset += relaEnt) {
                Address relocation = address(table + offset);
                long target = q64(relocation);
                long info = q64(relocation.add(8));
                long addend = q64(relocation.add(16));
                int type = (int) (info & 0xffffffffL);
                long symbolIndex = info >>> 32;
                if (type == 8) continue;
                if (type != 6 && type != 7 && type != 1) {
                    log.appendMsg("PS5 ELF analyzer: unsupported " + kind + " relocation type 0x" + Integer.toHexString(type));
                    continue;
                }
                if (symbolIndex >= symbols.size()) continue;
                SymbolInfo symbol = symbols.get((int) symbolIndex);
                long value = symbol.value != 0 ? symbol.value : q64(address(target));
                if (value != 0 && value != BAD && symbol.name != null) {
                    label(value, symbol.name, "PS5 " + kind + " relocation at 0x" + Long.toHexString(target));
                }
                if (type == 1 && addend != 0 && symbol.name != null) {
                    addComment(target, "PS5 relocation addend: 0x" + Long.toHexString(addend));
                }
            }
        }

        private void parseProcessParam(long start, long size) throws Exception {
            if (size < 8) return;
            addComment(start, "PS5 process parameter size: 0x" + Long.toHexString(q64(address(start))));
            String magic = ascii(start + 8, 4);
            if (!"ORBI".equals(magic)) {
                log.appendMsg("PS5 ELF analyzer: invalid sceProcessParam magic: " + magic);
                return;
            }
            addComment(start, "PS5 sceProcessParam: ORBI, entries=" + u32(address(start + 12)) +
                    ", SDK=0x" + Long.toHexString(u32(address(start + 16))));
        }

        private void tryParseProcessParam(long start, long size) {
            try { parseProcessParam(start, size); }
            catch (Exception e) { log.appendMsg("PS5 ELF analyzer: unable to read process parameters: " + e.getMessage()); }
        }

        private void parseModuleParam(long start, long size) throws Exception {
            if (size < 8) return;
            String magic = ascii(start + 8, 4);
            if (!"\u00bf\u00f4\u0013<".equals(magic)) {
                addComment(start, "PS5 module parameter block (unknown magic " + magic + ")");
                return;
            }
            addComment(start, "PS5 sceModuleParam: entries=" + u32(address(start + 12)) +
                    ", SDK=0x" + Long.toHexString(q64(address(start + 16))));
        }

        private void tryParseModuleParam(long start, long size) {
            try { parseModuleParam(start, size); }
            catch (Exception e) { log.appendMsg("PS5 ELF analyzer: unable to read module parameters: " + e.getMessage()); }
        }

        private void parseCommentSegment(long start, long size) throws Exception {
            long cursor = start;
            long end = start + size;
            while (cursor + 12 <= end) {
                String key = ascii(cursor, 4).replace("\0", "").trim();
                long length = u32(address(cursor + 8));
                cursor += 12;
                if (length > end - cursor) {
                    log.appendMsg("PS5 ELF analyzer: truncated comment segment");
                    return;
                }
                String value = ascii(cursor, length).replace("\0", "");
                addComment(start, "PS5 metadata " + key + ": " + value);
                cursor += length;
            }
        }

        private void tryParseCommentSegment(long start, long size) {
            try { parseCommentSegment(start, size); }
            catch (Exception e) { log.appendMsg("PS5 ELF analyzer: unable to read comment segment: " + e.getMessage()); }
        }

        private void parseVersionSegment(long start, long size) throws Exception {
            long cursor = start;
            long end = start + size;
            while (cursor + 4 <= end) {
                int length = u16(address(cursor + 2));
                cursor += 4;
                if (length == 0) continue;
                if (length > end - cursor) {
                    log.appendMsg("PS5 ELF analyzer: truncated version segment");
                    return;
                }
                int type = program.getMemory().getByte(address(cursor)) & 0xff;
                addComment(start, "PS5 version record type 0x" + Integer.toHexString(type) + ": " + ascii(cursor + 1, length - 1));
                cursor += length;
            }
        }

        private void tryParseVersionSegment(long start, long size) {
            try { parseVersionSegment(start, size); }
            catch (Exception e) { log.appendMsg("PS5 ELF analyzer: unable to read version segment: " + e.getMessage()); }
        }

        private void tryParseEhFrameHeader(long start, long size) {
            try {
                if (size < 4) return;
                Address cursor = address(start);
                int version = program.getMemory().getByte(cursor) & 0xff;
                int frameEncoding = program.getMemory().getByte(cursor.add(1)) & 0xff;
                int countEncoding = program.getMemory().getByte(cursor.add(2)) & 0xff;
                int tableEncoding = program.getMemory().getByte(cursor.add(3)) & 0xff;
                addComment(start, "PS5 EH frame header: version=" + version + ", frame=0x" +
                        Integer.toHexString(frameEncoding) + ", count=0x" + Integer.toHexString(countEncoding) +
                        ", table=0x" + Integer.toHexString(tableEncoding));
                EncodedValue frame = readEncoded(cursor.add(4), frameEncoding, start);
                EncodedValue count = readEncoded(frame.next, countEncoding, start);
                long entries = Math.min(count.value, (size - (count.next.getOffset() - start)) / 8);
                Address entry = count.next;
                for (long i = 0; i < entries; i++) {
                    EncodedValue location = readEncoded(entry, tableEncoding, start);
                    EncodedValue fde = readEncoded(location.next, tableEncoding, start);
                    if (location.value != 0) {
                        addComment(location.value, "PS5 EH function table entry");
                        parseFdeFunction(fde.value);
                    }
                    entry = fde.next;
                }
            }
            catch (Exception e) {
                log.appendMsg("PS5 ELF analyzer: unable to parse EH frame header: " + e.getMessage());
            }
        }

        private void parseFdeFunction(long fdeAddress) throws Exception {
            Address fde = address(fdeAddress);
            long length = u32(fde);
            if (length < 8 || length > 0x100000 || !program.getMemory().contains(fde.add(length + 4))) return;
            long cieOffset = u32(fde.add(4));
            long cieAddress = fdeAddress + 4 - cieOffset;
            int encoding = findFdeEncoding(cieAddress);
            if (encoding < 0) return;
            EncodedValue initial = readEncoded(fde.add(8), encoding, fdeAddress + 8);
            EncodedValue range = readEncoded(initial.next, encoding & 0x0f, fdeAddress + 8);
            if (initial.value == 0 || range.value <= 0 || initial.value > Long.MAX_VALUE - range.value) return;
            Address functionStart = address(initial.value);
            Address functionEnd = address(initial.value + range.value - 1);
            if (!program.getMemory().contains(functionStart) || !program.getMemory().contains(functionEnd)) return;
            FunctionManager manager = program.getFunctionManager();
            if (manager.getFunctionAt(functionStart) == null) {
                try {
                    manager.createFunction("eh_" + Long.toHexString(initial.value), functionStart,
                            new AddressSet(functionStart, functionEnd), SourceType.ANALYSIS);
                }
                catch (Exception e) {
                    log.appendMsg("PS5 ELF analyzer: unable to create EH function at 0x" +
                            Long.toHexString(initial.value) + ": " + e.getMessage());
                }
            }
        }

        private int findFdeEncoding(long cieAddress) throws Exception {
            Address cie = address(cieAddress);
            long length = u32(cie);
            if (length < 8 || length > 0x100000) return -1;
            Address cursor = cie.add(8);
            int version = program.getMemory().getByte(cursor) & 0xff;
            cursor = cursor.add(1);
            StringBuilder augmentation = new StringBuilder();
            int byteValue;
            do {
                byteValue = program.getMemory().getByte(cursor) & 0xff;
                cursor = cursor.add(1);
                if (byteValue != 0) augmentation.append((char) byteValue);
            } while (byteValue != 0 && augmentation.length() < 32);
            LebValue codeAlignment = readLeb(cursor, false);
            cursor = codeAlignment.next;
            LebValue dataAlignment = readLeb(cursor, true);
            cursor = dataAlignment.next;
            cursor = cursor.add(version == 1 ? 1 : readLeb(cursor, false).next.getOffset() - cursor.getOffset());
            if (!augmentation.toString().startsWith("z")) return 0;
            LebValue augmentationLength = readLeb(cursor, false);
            cursor = augmentationLength.next;
            Address augmentationEnd = cursor.add(augmentationLength.value);
            for (int i = 1; i < augmentation.length() && cursor.getOffset() < augmentationEnd.getOffset(); i++) {
                char item = augmentation.charAt(i);
                if (item == 'R') return program.getMemory().getByte(cursor) & 0xff;
                if (item == 'L') cursor = cursor.add(1);
                else if (item == 'P') {
                    int personalityEncoding = program.getMemory().getByte(cursor) & 0xff;
                    cursor = cursor.add(1);
                    cursor = readEncoded(cursor, personalityEncoding, cursor.getOffset()).next;
                }
            }
            return 0;
        }

        private EncodedValue readEncoded(Address start, int encoding, long dataBase) throws Exception {
            int format = encoding & 0x0f;
            long value;
            Address next = start;
            if (format == 0x00) { value = q64(next); next = next.add(8); }
            else if (format == 0x03) { value = u32(next); next = next.add(4); }
            else if (format == 0x04) { value = q64(next); next = next.add(8); }
            else if (format == 0x0b) { value = program.getMemory().getInt(next); next = next.add(4); }
            else if (format == 0x0c) { value = q64(next); next = next.add(8); }
            else if (format == 0x01 || format == 0x09) {
                long result = 0;
                int shift = 0;
                int byteValue;
                do {
                    byteValue = program.getMemory().getByte(next) & 0xff;
                    result |= (long) (byteValue & 0x7f) << shift;
                    shift += 7;
                    next = next.add(1);
                } while ((byteValue & 0x80) != 0 && shift < 64);
                value = format == 0x09 && shift < 64 && (byteValue & 0x40) != 0 ? result - (1L << shift) : result;
            }
            else throw new IOException("unsupported EH encoding 0x" + Integer.toHexString(encoding));
            int application = encoding & 0x70;
            if (application == 0x10) value += start.getOffset();
            else if (application == 0x30) value += dataBase;
            else if (application != 0) throw new IOException("unsupported EH application 0x" + Integer.toHexString(application));
            if ((encoding & 0x80) != 0 && value != 0) value = q64(address(value));
            return new EncodedValue(value, next);
        }

        private LebValue readLeb(Address start, boolean signed) throws Exception {
            long result = 0;
            int shift = 0;
            int byteValue;
            do {
                byteValue = program.getMemory().getByte(start.add(shift / 7)) & 0xff;
                result |= (long) (byteValue & 0x7f) << shift;
                shift += 7;
            } while ((byteValue & 0x80) != 0 && shift < 64);
            if (signed && shift < 64 && (byteValue & 0x40) != 0) result -= 1L << shift;
            return new LebValue(result, start.add((shift + 6) / 7));
        }

        private String ascii(long start, long length) throws Exception {
            StringBuilder result = new StringBuilder();
            for (long i = 0; i < length && i < 0x10000; i++) {
                result.append((char) (program.getMemory().getByte(address(start + i)) & 0xff));
            }
            return result.toString();
        }

        private String sanitize(String value) {
            return value.replaceAll("[^a-zA-Z0-9_]", "_");
        }

        private void label(long value, String name, String comment) throws Exception {
            Address target = address(value);
            if (program.getMemory().contains(target)) {
                try {
                    program.getSymbolTable().createLabel(target, name, SourceType.IMPORTED);
                }
                catch (Exception e) {
                    log.appendMsg("PS5 ELF analyzer: unable to create label " + name + ": " + e.getMessage());
                }
            }
            addComment(value, comment);
        }

        private void addComment(long value, String comment) throws Exception {
            addComment(address(value), comment);
        }

        private void addComment(Address target, String comment) throws Exception {
            if (!program.getMemory().contains(target)) return;
            CodeUnit codeUnit = program.getListing().getCodeUnitAt(target);
            String existing = codeUnit == null ? null : codeUnit.getComment(CodeUnit.PRE_COMMENT);
            if (existing != null && !existing.contains(comment)) comment = existing + "\n" + comment;
            program.getListing().setComment(target, CodeUnit.PRE_COMMENT, comment);
        }

        private String stringAt(long value) throws Exception {
            Address target = address(value);
            StringBuilder result = new StringBuilder();
            long limit = strtabSize > 0 && value >= strtab ? strtabSize - (value - strtab) : 0x10000;
            for (long i = 0; i < limit && i < 0x10000 && program.getMemory().contains(target.add(i)); i++) {
                int b = program.getMemory().getByte(target.add(i)) & 0xff;
                if (b == 0) break;
                result.append((char) b);
            }
            return result.toString();
        }

        private long q64(Address address) throws Exception { return program.getMemory().getLong(address); }
        private long u32(Address address) throws Exception { return program.getMemory().getInt(address) & 0xffffffffL; }
        private int u16(Address address) throws Exception { return program.getMemory().getShort(address) & 0xffff; }
        private Address address(long value) { return program.getAddressFactory().getDefaultAddressSpace().getAddress(value); }
    }

    private static final class EncodedValue {
        final long value;
        final Address next;

        EncodedValue(long value, Address next) {
            this.value = value;
            this.next = next;
        }
    }

    private static final class LebValue {
        final long value;
        final Address next;

        LebValue(long value, Address next) {
            this.value = value;
            this.next = next;
        }
    }

    private static final class ObjectInfo {
        String name = "unknown";
        String version = "0.0";
        long nameOffset = -1;
        long attributes;
        boolean export;

        String describe() {
            return name + " v" + version + " attrs=0x" + Long.toHexString(attributes) +
                    (export ? " export" : " import");
        }
    }

    private static final class SymbolInfo {
        final String name;
        final String encodedName;
        final long value;
        final long size;
        final int section;
        final boolean function;

        SymbolInfo(String name, String encodedName, long value, long size, int section, boolean function) {
            this.name = name;
            this.encodedName = encodedName;
            this.value = value;
            this.size = size;
            this.section = section;
            this.function = function;
        }
    }

    private static long decode(String value) {
        if (value.length() == 0 || value.length() > 11) return BAD;
        long result = 0;
        for (int i = 0; i < value.length(); i++) {
            int digit = NID_ALPHABET.indexOf(value.charAt(i));
            if (digit < 0) return BAD;
            if (i == value.length() - 1 && value.length() == 11) result = (result << 4) | (digit >> 2);
            else result = (result << 6) | digit;
        }
        return result;
    }

    private static long decodeObjectId(String value) {
        if (value.length() == 0 || value.length() > 4) return BAD;
        long result = 0;
        for (int i = 0; i < value.length(); i++) {
            int digit = NID_ALPHABET.indexOf(value.charAt(i));
            if (digit < 0) return BAD;
            result = (result << 6) | digit;
        }
        return result;
    }

    private static Map<Long, String> loadKnownNids() {
        Map<Long, String> result = new HashMap<>();
        InputStream stream = Ps5ElfAnalyzer.class.getResourceAsStream("/ps5_symbols.txt");
        if (stream == null) return result;
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(stream, StandardCharsets.UTF_8))) {
            String line;
            while ((line = reader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty() || line.startsWith("#")) continue;
                String name = line.split(":", 2)[0].trim();
                long nid = encodeNid(name);
                if (nid != BAD) result.put(nid, name);
                String alternate = name.startsWith("_") ? name.substring(1) : "_" + name;
                nid = encodeNid(alternate);
                if (nid != BAD) result.put(nid, alternate);
            }
        }
        catch (IOException ignored) {
            // An absent optional database does not prevent metadata analysis.
        }
        return result;
    }

    private static long encodeNid(String name) {
        try {
            java.security.MessageDigest digest = java.security.MessageDigest.getInstance("SHA-1");
            byte[] suffix = new byte[] {0x51, (byte) 0x8d, 0x64, (byte) 0xa6, 0x35, (byte) 0xde, (byte) 0xd8, (byte) 0xc1, (byte) 0xe6, (byte) 0xb0, 0x39, (byte) 0xb1, (byte) 0xc3, (byte) 0xe5, 0x52, 0x30};
            digest.update(name.getBytes(StandardCharsets.US_ASCII));
            byte[] hash = digest.digest(suffix);
            long result = 0;
            for (int i = 7; i >= 0; i--) result = (result << 8) | (hash[i] & 0xffL);
            return result;
        }
        catch (Exception e) {
            return BAD;
        }
    }
}