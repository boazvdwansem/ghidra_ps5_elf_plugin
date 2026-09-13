package ps5.ghidra;

import ghidra.app.services.AbstractAnalyzer;
import ghidra.app.services.AnalysisPriority;
import ghidra.app.services.AnalyzerType;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.CodeUnit;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolIterator;
import ghidra.program.model.symbol.SymbolTable;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
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
    private static final long DT_RELACOUNT = 0x6ffffff9L;

    private static final String NID_ALPHABET =
            "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-";
    private static final long BAD = Long.MIN_VALUE;

    private static Map<Long, String> KNOWN_NIDS = null;

    public Ps5ElfAnalyzer() {
        super("PS5 ELF Analyzer", "Decodes PS5 ELF metadata and NID symbols", AnalyzerType.BYTE_ANALYZER);
        setPriority(AnalysisPriority.FORMAT_ANALYSIS.before());
        setSupportsOneTimeAnalysis();
    }

    private static Address getElfHeaderAddress(Program program) {
        MemoryBlock block = program.getMemory().getBlock("_elfHeader");
        if (block != null) {
            return block.getStart();
        }
        Address base = program.getImageBase();
        if (base != null && isElfHeaderAt(program, base)) {
            return base;
        }
        return null;
    }

    private static boolean isElfHeaderAt(Program program, Address addr) {
        try {
            return (program.getMemory().getByte(addr) & 0xff) == 0x7f &&
                    program.getMemory().getByte(addr.add(1)) == 'E' &&
                    program.getMemory().getByte(addr.add(2)) == 'L' &&
                    program.getMemory().getByte(addr.add(3)) == 'F';
        }
        catch (Exception e) {
            return false;
        }
    }

    private static File resolveExecutableFile(Program program) {
        String path = program.getExecutablePath();
        if (path == null || path.isEmpty()) return null;
        File f = new File(path);
        if (f.exists() && f.isFile()) return f;
        if (path.startsWith("/") && path.length() > 2 && path.charAt(2) == ':') {
            File fWin = new File(path.substring(1));
            if (fWin.exists() && fWin.isFile()) return fWin;
        }
        if (path.startsWith("file:/")) {
            try {
                File fUri = new File(new java.net.URI(path));
                if (fUri.exists()) return fUri;
            } catch (Exception ignored) {}
        }
        return null;
    }

    private static boolean checkExecutableFile(Program program) {
        File file = resolveExecutableFile(program);
        if (file == null) return false;
        try (RandomAccessFile raf = new RandomAccessFile(file, "r")) {
            byte[] header = new byte[64];
            if (raf.read(header) != 64) return false;
            if (header[0] != 0x7f || header[1] != 'E' || header[2] != 'L' || header[3] != 'F') return false;
            int identClass = header[4] & 0xff;
            int identData = header[5] & 0xff;
            int e_type = ((header[17] & 0xff) << 8) | (header[16] & 0xff);
            int e_machine = ((header[19] & 0xff) << 8) | (header[18] & 0xff);
            return identClass == 2 && identData == 1 && e_machine == EM_X86_64 &&
                    (e_type == ET_SCE_EXEC_ASLR || e_type == ET_SCE_DYNAMIC);
        }
        catch (Exception e) {
            return false;
        }
    }

    @Override
    public boolean canAnalyze(Program program) {
        try {
            Address headerAddr = getElfHeaderAddress(program);
            if (headerAddr != null && isElfHeaderAt(program, headerAddr)) {
                int identClass = program.getMemory().getByte(headerAddr.add(4)) & 0xff;
                int identData = program.getMemory().getByte(headerAddr.add(5)) & 0xff;
                int e_type = u16(program, headerAddr.add(16));
                int e_machine = u16(program, headerAddr.add(18));
                return identClass == 2 && identData == 1 && e_machine == EM_X86_64 &&
                        (e_type == ET_SCE_EXEC_ASLR || e_type == ET_SCE_DYNAMIC);
            }
            return checkExecutableFile(program);
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
            log.appendMsg("PS5 ELF analyzer error: " + e.getMessage());
            return false;
        }
    }

    private static int u16(Program program, Address address) throws Exception {
        return program.getMemory().getShort(address) & 0xffff;
    }

    private static final class Phdr {
        long type;
        long flags;
        long offset;
        long vaddr;
        long paddr;
        long filesz;
        long memsz;
        long align;
    }

    private static final class DecodedSymbol {
        final String name;
        final String moduleName;
        final String libraryName;
        final String comment;
        final long nid;

        DecodedSymbol(String name, String moduleName, String libraryName, String comment, long nid) {
            this.name = name;
            this.moduleName = moduleName;
            this.libraryName = libraryName;
            this.comment = comment;
            this.nid = nid;
        }
    }

    private static final class Context {
        private final Program program;
        private final TaskMonitor monitor;
        private final MessageLog log;
        private final Map<Long, ObjectInfo> modules = new HashMap<>();
        private final Map<Long, ObjectInfo> libraries = new HashMap<>();
        private final Map<Long, String> knownNids = getKnownNids();
        private final Set<Long> functions = new HashSet<>();
        private final List<SymbolInfo> symbols = new ArrayList<>();
        private long dynamicSize;
        private long strtabSize;
        private long rela;
        private long relaSize;
        private long relaEnt = 24;
        private long relaCount = 0;
        private long jmprel;
        private long jmprelSize;
        private long pltGot = 0;
        private long initProc = 0;
        private long finiProc = 0;
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
            monitor.setMessage("PS5 ELF: loading program headers...");
            List<Phdr> phdrs = loadProgramHeaders();
            Phdr dynamicPhdr = null;

            for (Phdr ph : phdrs) {
                if (ph.type == PT_DYNAMIC) {
                    dynamicPhdr = ph;
                    dynamicSize = ph.memsz;
                }
                if (ph.type == PT_SCE_PROCPARAM || ph.type == PT_SCE_MODULE_PARAM ||
                        ph.type == PT_SCE_COMMENT || ph.type == PT_SCE_VERSION || ph.type == PT_GNU_EH_FRAME) {
                    addComment(ph.vaddr, "PS5 program header type 0x" + Long.toHexString(ph.type));
                    if (ph.type == PT_SCE_PROCPARAM) tryParseProcessParam(ph.vaddr, ph.filesz);
                    if (ph.type == PT_SCE_MODULE_PARAM) tryParseModuleParam(ph.vaddr, ph.filesz);
                    if (ph.type == PT_SCE_COMMENT) tryParseCommentSegment(readSegmentData(ph));
                    if (ph.type == PT_SCE_VERSION) tryParseVersionSegment(readSegmentData(ph));
                    if (ph.type == PT_GNU_EH_FRAME) tryParseEhFrameHeader(ph.vaddr, ph.filesz);
                }
            }

            if (dynamicPhdr == null || dynamicPhdr.vaddr == 0) {
                log.appendMsg("PS5 ELF analyzer: dynamic program header not found");
                return;
            }

            monitor.setMessage("PS5 ELF: parsing dynamic tags...");
            parseDynamic(dynamicPhdr.vaddr);
            resolveMetadata();

            if (strtab == 0 || symtab == 0 || syment < 24) {
                log.appendMsg("PS5 ELF analyzer: dynamic strtab or symtab not found");
                return;
            }

            monitor.setMessage("PS5 ELF: decoding symbols...");
            int count = (int) (symtabSize / syment);
            for (int i = 0; i < count; i++) {
                monitor.checkCanceled();
                parseSymbol(i, symtab + (long) i * syment);
            }

            monitor.setMessage("PS5 ELF: applying relocations...");
            applyRelocations(rela, relaSize, "RELA", relaCount);
            applyRelocations(jmprel, jmprelSize, "JMPREL", 0);

            // Fix up init / fini procedures
            if (initProc != 0 && program.getMemory().contains(address(initProc))) {
                label(initProc, "_init", "PS5 init procedure");
                if (program.getFunctionManager().getFunctionAt(address(initProc)) == null) {
                    try {
                        program.getFunctionManager().createFunction("_init", address(initProc),
                                new AddressSet(address(initProc), address(initProc + 15)), SourceType.IMPORTED);
                    } catch (Exception ignored) {}
                }
            }
            if (finiProc != 0 && program.getMemory().contains(address(finiProc))) {
                label(finiProc, "_fini", "PS5 fini procedure");
                if (program.getFunctionManager().getFunctionAt(address(finiProc)) == null) {
                    try {
                        program.getFunctionManager().createFunction("_fini", address(finiProc),
                                new AddressSet(address(finiProc), address(finiProc + 15)), SourceType.IMPORTED);
                    } catch (Exception ignored) {}
                }
            }

            markNoReturnFunctions();

            if (soname != null) addComment(program.getImageBase(), "PS5 SONAME: " + soname);
            if (originalFilename != null) addComment(program.getImageBase(), "PS5 original filename: " + originalFilename);
        }

        private List<Phdr> loadProgramHeaders() throws Exception {
            List<Phdr> phdrs = new ArrayList<>();
            MemoryBlock phdrBlock = program.getMemory().getBlock("_elfProgramHeaders");
            if (phdrBlock != null && phdrBlock.getSize() >= 56) {
                int count = (int) (phdrBlock.getSize() / 56);
                Address start = phdrBlock.getStart();
                for (int i = 0; i < count; i++) {
                    Address ph = start.add((long) i * 56);
                    Phdr p = new Phdr();
                    p.type = u32(ph);
                    p.flags = u32(ph.add(4));
                    p.offset = q64(ph.add(8));
                    p.vaddr = q64(ph.add(16));
                    p.paddr = q64(ph.add(24));
                    p.filesz = q64(ph.add(32));
                    p.memsz = q64(ph.add(40));
                    p.align = q64(ph.add(48));
                    phdrs.add(p);
                }
                return phdrs;
            }

            File file = resolveExecutableFile(program);
            if (file != null) {
                try (RandomAccessFile raf = new RandomAccessFile(file, "r")) {
                    raf.seek(32);
                    long phoff = Long.reverseBytes(raf.readLong());
                    raf.seek(54);
                    int phentsize = Short.reverseBytes(raf.readShort()) & 0xffff;
                    int phnum = Short.reverseBytes(raf.readShort()) & 0xffff;
                    if (phoff > 0 && phentsize >= 56 && phnum > 0) {
                        for (int i = 0; i < phnum; i++) {
                            raf.seek(phoff + (long) i * phentsize);
                            byte[] buf = new byte[56];
                            if (raf.read(buf) == 56) {
                                ByteBuffer bb = ByteBuffer.wrap(buf).order(ByteOrder.LITTLE_ENDIAN);
                                Phdr p = new Phdr();
                                p.type = bb.getInt() & 0xffffffffL;
                                p.flags = bb.getInt() & 0xffffffffL;
                                p.offset = bb.getLong();
                                p.vaddr = bb.getLong();
                                p.paddr = bb.getLong();
                                p.filesz = bb.getLong();
                                p.memsz = bb.getLong();
                                p.align = bb.getLong();
                                phdrs.add(p);
                            }
                        }
                    }
                }
            }
            return phdrs;
        }

        private byte[] readSegmentData(Phdr phdr) {
            if (phdr.filesz <= 0 || phdr.filesz > 0x10000000L) return null;
            File file = resolveExecutableFile(program);
            if (file != null) {
                try (RandomAccessFile raf = new RandomAccessFile(file, "r")) {
                    raf.seek(phdr.offset);
                    byte[] data = new byte[(int) phdr.filesz];
                    raf.readFully(data);
                    return data;
                }
                catch (Exception ignored) {}
            }
            if (phdr.vaddr != 0) {
                Address a = address(phdr.vaddr);
                if (program.getMemory().contains(a)) {
                    byte[] data = new byte[(int) phdr.filesz];
                    try {
                        program.getMemory().getBytes(a, data);
                        return data;
                    }
                    catch (Exception ignored) {}
                }
            }
            for (MemoryBlock mb : program.getMemory().getBlocks()) {
                if (mb.isOverlay() && mb.getSize() == phdr.filesz) {
                    byte[] data = new byte[(int) phdr.filesz];
                    try {
                        program.getMemory().getBytes(mb.getStart(), data);
                        return data;
                    }
                    catch (Exception ignored) {}
                }
            }
            return null;
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
                    case (int) DT_RELACOUNT: relaCount = value; break;
                    case (int) DT_JMPREL: jmprel = value; break;
                    case (int) DT_PLTRELSZ: jmprelSize = value; break;
                    case (int) DT_PLTGOT: pltGot = value; break;
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
                    case (int) DT_INIT: initProc = value; addComment(value, "PS5 init procedure"); break;
                    case (int) DT_FINI: finiProc = value; addComment(value, "PS5 fini procedure"); break;
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

        private void parseSymbol(int index, long address) throws Exception {
            Address symbol = address(address);
            int nameOffset = (int) u32(symbol);
            int info = program.getMemory().getByte(symbol.add(4)) & 0xff;
            int shndx = u16(symbol.add(6));
            long value = q64(symbol.add(8));
            long size = q64(symbol.add(16));
            int type = info & 0xf;
            boolean isFunc = (type == 2);
            boolean isObject = (type == 1);

            if (nameOffset == 0 || (!isFunc && !isObject)) {
                symbols.add(new SymbolInfo(null, null, value, size, shndx, isFunc, null));
                return;
            }

            String encoded = stringAt(strtab + nameOffset);
            DecodedSymbol decoded = decodeSymbol(encoded, isFunc);
            symbols.add(new SymbolInfo(decoded.name, encoded, value, size, shndx, isFunc, decoded));

            renameExistingGhidraSymbols(encoded, decoded.name, decoded.comment);

            if (decoded.name != null && value != 0 && shndx != 0) {
                label(value, decoded.name, decoded.comment);
                if (isFunc && size > 0 && functions.add(value)) {
                    FunctionManager manager = program.getFunctionManager();
                    Function fn = manager.getFunctionAt(address(value));
                    if (fn == null) {
                        manager.createFunction(decoded.name, address(value),
                                new AddressSet(address(value), address(value + size - 1)), SourceType.IMPORTED);
                    } else if (fn.getName().startsWith("FUN_") || fn.getName().equals(encoded)) {
                        fn.setName(decoded.name, SourceType.IMPORTED);
                    }
                }
            }
        }

        private void renameExistingGhidraSymbols(String encoded, String newName, String comment) {
            SymbolTable symTable = program.getSymbolTable();
            SymbolIterator it = symTable.getSymbols(encoded);
            while (it.hasNext()) {
                Symbol s = it.next();
                try {
                    s.setName(newName, SourceType.IMPORTED);
                    addComment(s.getAddress(), comment);
                } catch (Exception e) {
                    log.appendMsg("PS5 ELF analyzer: unable to rename symbol " + encoded + " to " + newName + ": " + e.getMessage());
                }
            }
        }

        private DecodedSymbol decodeSymbol(String encoded, boolean isFunc) {
            String[] parts = encoded.split("#", -1);
            if (parts.length != 3) {
                return new DecodedSymbol(encoded, null, null, encoded, 0);
            }
            long nid = decode(parts[0]);
            long library = decodeObjectId(parts[1]);
            long module = decodeObjectId(parts[2]);
            ObjectInfo mod = modules.get(module);
            ObjectInfo lib = libraries.get(library);
            if (nid == BAD || mod == null || lib == null) {
                return new DecodedSymbol(encoded, null, null, encoded, nid);
            }

            String modName = sanitize(mod.name);
            String libName = sanitize(lib.name);
            String known = knownNids.get(nid);
            String finalName;
            if (known != null) {
                finalName = known;
            } else {
                String suffix = isFunc ? "f" : "o";
                if (modName.equalsIgnoreCase(libName)) {
                    finalName = String.format("nid%s_%s_0x%016x", suffix, modName, nid);
                } else {
                    finalName = String.format("nid%s_%s_%s_0x%016x", suffix, modName, libName, nid);
                }
            }

            String comment = String.format("PS5 %s:\n  Module: %s\n  Library: %s\n  NID: 0x%016x\n  Encoded: %s",
                    isFunc ? "Function" : "Object", mod.name, lib.name, nid, encoded);
            return new DecodedSymbol(finalName, mod.name, lib.name, comment, nid);
        }

        private Address findPltBase(long gotPltAddr) {
            if (gotPltAddr == 0) return null;
            Address gotPlt1 = address(gotPltAddr + 8);
            ReferenceIterator refs = program.getReferenceManager().getReferencesTo(gotPlt1);
            while (refs.hasNext()) {
                Reference r = refs.next();
                Address from = r.getFromAddress();
                long plt0Offset = from.getOffset() & ~0xfL;
                Address pltBase = address(plt0Offset + 16);
                try {
                    if ((program.getMemory().getByte(pltBase) & 0xff) == 0xff &&
                        (program.getMemory().getByte(pltBase.add(1)) & 0xff) == 0x25) {
                        return pltBase;
                    }
                } catch (Exception ignored) {}
            }
            return null;
        }

        private void applyRelocations(long table, long size, String kind, long skipCount) throws Exception {
            if (table == 0 || size == 0 || relaEnt < 24) return;
            long startOffset = 0;
            if (skipCount > 0 && skipCount * relaEnt < size) {
                startOffset = skipCount * relaEnt;
            }
            boolean isJmpRel = "JMPREL".equals(kind);
            Address pltBase = isJmpRel ? findPltBase(pltGot) : null;

            for (long offset = startOffset; offset + relaEnt <= size; offset += relaEnt) {
                monitor.checkCanceled();
                Address relocation = address(table + offset);
                long target = q64(relocation);
                long info = q64(relocation.add(8));
                long addend = q64(relocation.add(16));
                int type = (int) (info & 0xffffffffL);
                long symbolIndex = info >>> 32;
                if (type == 8) continue;
                if (symbolIndex >= symbols.size()) continue;
                SymbolInfo symbol = symbols.get((int) symbolIndex);
                if (symbol == null || symbol.name == null) continue;

                if (type == 7) {
                    // Update PLT function directly if PLT base is known
                    int entryIndex = (int) (offset / relaEnt);
                    Address funcEa = pltBase != null ? pltBase.add((long) entryIndex * 16L) : null;
                    if (funcEa != null && program.getMemory().contains(funcEa)) {
                        // Ensure instructions are disassembled
                        if (program.getListing().getInstructionAt(funcEa) == null) {
                            ghidra.app.cmd.disassemble.DisassembleCommand disCmd =
                                    new ghidra.app.cmd.disassemble.DisassembleCommand(funcEa, null, true);
                            disCmd.applyTo(program);
                        }

                        // Fix any overlapping function that mistakenly swallowed this PLT entry
                        Function containing = program.getFunctionManager().getFunctionContaining(funcEa);
                        if (containing != null && !containing.getEntryPoint().equals(funcEa)) {
                            try {
                                AddressSet origBody = new AddressSet(containing.getBody());
                                origBody.delete(new AddressSet(funcEa, funcEa.add(15)));
                                containing.setBody(origBody);
                            } catch (Exception ignored) {}
                        }

                        Function pltFn = program.getFunctionManager().getFunctionAt(funcEa);
                        if (pltFn == null) {
                            try {
                                pltFn = program.getFunctionManager().createFunction(symbol.name, funcEa,
                                        new AddressSet(funcEa, funcEa.add(15)), SourceType.IMPORTED);
                            } catch (Exception ignored) {}
                        } else if (pltFn.getName().startsWith("FUN_") || pltFn.getName().contains("#")) {
                            try {
                                pltFn.setName(symbol.name, SourceType.IMPORTED);
                            } catch (Exception ignored) {}
                        }

                        // Link as thunk if an external function exists for this symbol
                        if (pltFn != null && !pltFn.isThunk()) {
                            try {
                                for (Symbol s : program.getSymbolTable().getSymbols(symbol.name)) {
                                    if (s.isExternal()) {
                                        Function extFn = program.getFunctionManager().getFunctionAt(s.getAddress());
                                        if (extFn != null) {
                                            pltFn.setThunkedFunction(extFn);
                                            break;
                                        }
                                    }
                                }
                            } catch (Exception ignored) {}
                        }

                        if (pltFn != null) {
                            addComment(funcEa, symbol.decoded != null ? symbol.decoded.comment : "PS5 PLT stub for " + symbol.name);
                        }
                    }

                    // Check xrefs to target GOT slot as fallback
                    ReferenceIterator refs = program.getReferenceManager().getReferencesTo(address(target));
                    while (refs.hasNext()) {
                        Reference r = refs.next();
                        Address from = r.getFromAddress();
                        Function pltFn = program.getFunctionManager().getFunctionContaining(from);
                        if (pltFn != null && (pltFn.getName().startsWith("FUN_") || pltFn.getName().contains("#"))) {
                            try {
                                pltFn.setName(symbol.name, SourceType.IMPORTED);
                                addComment(pltFn.getEntryPoint(), symbol.decoded != null ? symbol.decoded.comment : "PS5 PLT stub for " + symbol.name);
                            } catch (Exception ignored) {}
                        }
                    }

                    Symbol gotSym = program.getSymbolTable().getPrimarySymbol(address(target));
                    if (gotSym == null || gotSym.getName().startsWith("DAT_") || gotSym.getName().contains("#")) {
                        label(target, symbol.name, "PS5 PLT got slot for " + symbol.name);
                    }
                } else if (type == 6 || type == 1) {
                    long value = symbol.value != 0 ? symbol.value : q64(address(target));
                    if (value != 0 && value != BAD) {
                        label(value, symbol.name, "PS5 " + kind + " relocation at 0x" + Long.toHexString(target));
                    }
                    if (type == 1 && addend != 0) {
                        addComment(target, "PS5 relocation addend: 0x" + Long.toHexString(addend));
                    }
                }
            }
        }

        private void markNoReturnFunctions() {
            String[] names = {
                "exit", "exit1", "abort", "__stack_chk_fail",
                "_ZNSt9bad_allocD0Ev", "_ZNSt9bad_allocD1Ev", "_ZNSt9bad_allocD2Ev", "_ZSt11_Xbad_allocv",
                "_ZNSt16invalid_argumentD0Ev", "_ZNSt16invalid_argumentD1Ev", "_ZNSt16invalid_argumentD2Ev", "_ZSt18_Xinvalid_argumentPKc",
                "_ZNSt12length_errorD0Ev", "_ZNSt12length_errorD1Ev", "_ZNSt12length_errorD2Ev", "_ZSt14_Xlength_errorPKc",
                "_ZNSt12out_of_rangeD0Ev", "_ZNSt12out_of_rangeD1Ev", "_ZNSt12out_of_rangeD2Ev", "_ZSt14_Xout_of_rangePKc",
                "_ZNSt14overflow_errorD0Ev", "_ZNSt14overflow_errorD1Ev", "_ZNSt14overflow_errorD2Ev", "_ZSt16_Xoverflow_errorPKc",
                "_ZNSt13runtime_errorD0Ev", "_ZNSt13runtime_errorD1Ev", "_ZNSt13runtime_errorD2Ev", "_ZSt15_Xruntime_errorPKc",
                "_ZNSt17bad_function_callD0Ev", "_ZNSt17bad_function_callD1Ev", "_ZNSt17bad_function_callD2Ev", "_ZSt19_Xbad_function_callv",
                "_ZNSt11regex_errorD0Ev", "_ZNSt11regex_errorD1Ev", "_ZNSt11regex_errorD2Ev",
                "_ZSt10_Rng_abortPKc", "_ZSt19_Throw_future_errorRKSt10error_code",
                "_ZSt25_Rethrow_future_exceptionPv", "_ZSt25_Rethrow_future_exceptionSt13exception_ptr"
            };
            for (String name : names) {
                SymbolIterator it = program.getSymbolTable().getSymbols(name);
                while (it.hasNext()) {
                    Symbol s = it.next();
                    Function f = program.getFunctionManager().getFunctionAt(s.getAddress());
                    if (f != null && !f.hasNoReturn()) {
                        f.setNoReturn(true);
                    }
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
            long entries = u32(address(start + 12));
            long sdk = u32(address(start + 16));
            addComment(start, String.format("PS5 sceProcessParam: ORBI, entries=%d, SDK=0x%08x", entries, sdk));
            if (size >= 0x40) {
                long procNameEa = q64(address(start + 24));
                long mainThreadNameEa = q64(address(start + 32));
                if (procNameEa != 0 && program.getMemory().contains(address(procNameEa))) {
                    String procName = stringAt(procNameEa);
                    if (!procName.isEmpty()) {
                        addComment(start, "PS5 Process Name: " + procName);
                        addComment(program.getImageBase(), "PS5 Process Name: " + procName);
                    }
                }
                if (mainThreadNameEa != 0 && program.getMemory().contains(address(mainThreadNameEa))) {
                    String threadName = stringAt(mainThreadNameEa);
                    if (!threadName.isEmpty()) {
                        addComment(start, "PS5 Main Thread: " + threadName);
                    }
                }
            }
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

        private void tryParseCommentSegment(byte[] data) {
            if (data == null || data.length < 12) return;
            try {
                ByteBuffer buf = ByteBuffer.wrap(data).order(ByteOrder.LITTLE_ENDIAN);
                while (buf.remaining() >= 12) {
                    byte[] keyBytes = new byte[4];
                    buf.get(keyBytes);
                    String key = new String(keyBytes, StandardCharsets.US_ASCII).replace("\0", "").trim();
                    int maxLen = buf.getInt();
                    int len = buf.getInt();
                    if (len < 0 || len > buf.remaining()) break;
                    byte[] valBytes = new byte[len];
                    buf.get(valBytes);
                    String val = new String(valBytes, StandardCharsets.UTF_8).replace("\0", "").trim();
                    if (!key.isEmpty() && !val.isEmpty()) {
                        addComment(program.getImageBase(), "PS5 metadata " + key + ": " + val);
                    }
                }
            } catch (Exception e) {
                log.appendMsg("PS5 ELF analyzer: unable to parse comment segment: " + e.getMessage());
            }
        }

        private void tryParseVersionSegment(byte[] data) {
            if (data == null || data.length < 4) return;
            try {
                ByteBuffer buf = ByteBuffer.wrap(data).order(ByteOrder.LITTLE_ENDIAN);
                while (buf.remaining() >= 4) {
                    int reserved = buf.getShort() & 0xffff;
                    int length = buf.getShort() & 0xffff;
                    if (length <= 0 || length > buf.remaining()) break;
                    int typeId = buf.get() & 0xff;
                    byte[] recBytes = new byte[length - 1];
                    buf.get(recBytes);
                    String recStr = new String(recBytes, StandardCharsets.US_ASCII).replace("\0", "").trim();
                    if (typeId == 0x8) {
                        addComment(program.getImageBase(), "PS5 library version: " + recStr);
                    } else if (!recStr.isEmpty()) {
                        addComment(program.getImageBase(), "PS5 version record [0x" + Integer.toHexString(typeId) + "]: " + recStr);
                    }
                }
            } catch (Exception e) {
                log.appendMsg("PS5 ELF analyzer: unable to parse version segment: " + e.getMessage());
            }
        }

        private void tryParseEhFrameHeader(long start, long size) {
            try {
                if (size < 4 || start == 0) return;
                Address cursor = address(start);
                if (!program.getMemory().contains(cursor)) return;
                int version = program.getMemory().getByte(cursor) & 0xff;
                int frameEncoding = program.getMemory().getByte(cursor.add(1)) & 0xff;
                int countEncoding = program.getMemory().getByte(cursor.add(2)) & 0xff;
                int tableEncoding = program.getMemory().getByte(cursor.add(3)) & 0xff;
                addComment(start, "PS5 EH frame header: version=" + version + ", frame=0x" +
                        Integer.toHexString(frameEncoding) + ", count=0x" + Integer.toHexString(countEncoding) +
                        ", table=0x" + Integer.toHexString(tableEncoding));
                EncodedValue frame = readEncoded(cursor.add(4), frameEncoding, start);
                EncodedValue count = readEncoded(frame.next, countEncoding, start);
                addComment(start, "PS5 EH frame entries: " + count.value);
                long maxEntries = Math.min(count.value, (size - (count.next.getOffset() - start)) / 8);
                long entries = Math.min(maxEntries, 5000L);
                Address entry = count.next;
                for (long i = 0; i < entries; i++) {
                    if (i % 1000 == 0) monitor.checkCanceled();
                    EncodedValue location = readEncoded(entry, tableEncoding, start);
                    EncodedValue fde = readEncoded(location.next, tableEncoding, start);
                    if (location.value != 0) {
                        parseFdeFunction(fde.value);
                    }
                    entry = fde.next;
                }
            }
            catch (CancelledException e) {
                // User cancelled analysis
            }
            catch (Exception e) {
                log.appendMsg("PS5 ELF analyzer: unable to parse EH frame header: " + e.getMessage());
            }
        }

        private void parseFdeFunction(long fdeAddress) throws Exception {
            Address fde = address(fdeAddress);
            if (!program.getMemory().contains(fde)) return;
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
                catch (Exception ignored) {}
            }
        }

        private int findFdeEncoding(long cieAddress) throws Exception {
            Address cie = address(cieAddress);
            if (!program.getMemory().contains(cie)) return -1;
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
            if (value == null) return "unknown";
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
        final DecodedSymbol decoded;

        SymbolInfo(String name, String encodedName, long value, long size, int section, boolean function, DecodedSymbol decoded) {
            this.name = name;
            this.encodedName = encodedName;
            this.value = value;
            this.size = size;
            this.section = section;
            this.function = function;
            this.decoded = decoded;
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

    private static synchronized Map<Long, String> getKnownNids() {
        if (KNOWN_NIDS == null) {
            KNOWN_NIDS = loadKnownNids();
        }
        return KNOWN_NIDS;
    }

    private static Map<Long, String> loadKnownNids() {
        Map<Long, String> result = new HashMap<>();
        InputStream stream = Ps5ElfAnalyzer.class.getResourceAsStream("/ps5_symbols.txt");
        if (stream == null) {
            stream = Ps5ElfAnalyzer.class.getClassLoader().getResourceAsStream("ps5_symbols.txt");
        }
        if (stream == null) {
            File f = new File("cfg/ps5_symbols.txt");
            if (f.exists()) {
                try {
                    stream = new FileInputStream(f);
                } catch (Exception ignored) {}
            }
        }
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
        catch (IOException ignored) {}
        return result;
    }

    private static long encodeNid(String name) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-1");
            byte[] suffix = new byte[] {0x51, (byte) 0x8d, 0x64, (byte) 0xa6, 0x35, (byte) 0xde, (byte) 0xd8, (byte) 0xc1, (byte) 0xe6, (byte) 0xb0, 0x39, (byte) 0xb1, (byte) 0xc3, (byte) 0xe5, (byte) 0x52, 0x30};
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
