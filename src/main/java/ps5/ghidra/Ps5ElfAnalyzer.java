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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.HashSet;
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
    private static final long DT_NULL = 0;
    private static final long DT_NEEDED = 1;
    private static final long DT_SONAME = 14;
    private static final long DT_INIT = 12;
    private static final long DT_FINI = 13;
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
        private long strtab;
        private long symtab;
        private long symtabSize;
        private long syment = 24;
        private String soname;

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
                long vaddr = q64(ph.add(16));
                if (type == PT_DYNAMIC) dynamic = vaddr;
                if (type == PT_SCE_PROCPARAM || type == PT_SCE_MODULE_PARAM || type == PT_GNU_EH_FRAME) {
                    addComment(vaddr, "PS5 program header type 0x" + Long.toHexString(type));
                }
            }
            if (dynamic == 0) return;
            parseDynamic(dynamic);
            if (strtab == 0 || symtab == 0 || syment < 24) return;
            int count = (int) (symtabSize / syment);
            for (int i = 0; i < count; i++) {
                monitor.checkCanceled();
                parseSymbol(symtab + i * syment);
            }
            if (soname != null) addComment(program.getImageBase(), "PS5 SONAME: " + soname);
        }

        private void parseDynamic(long address) throws Exception {
            for (int i = 0; i < 0x10000; i++) {
                Address entry = address(address + i * 16L);
                long tag = q64(entry);
                long value = q64(entry.add(8));
                if (tag == DT_NULL) return;
                switch ((int) tag) {
                    case (int) DT_STRTAB: strtab = value; break;
                    case (int) DT_SYMTAB: symtab = value; break;
                    case (int) DT_STRSZ: break;
                    case (int) DT_SYMENT: syment = value; break;
                    case (int) DT_SCE_SYMTABSZ: symtabSize = value; break;
                    case (int) DT_SONAME: soname = stringAt(strtab + value); break;
                    case (int) DT_NEEDED: addComment(address, "PS5 needed module: " + stringAt(strtab + value)); break;
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
                object.name = stringAt(strtab + (value & 0xffffffffL));
                object.version = ((value >>> 32) & 0xff) + "." + ((value >>> 40) & 0xff);
                addComment(program.getImageBase(), (module ? "PS5 module " : "PS5 library ") + id + ": " + object.name);
            }
            if (tag == DT_SCE_MODULE_ATTR || tag == DT_SCE_EXPORT_LIB_ATTR || tag == DT_SCE_IMPORT_LIB_ATTR) {
                long id = (value >>> 48) & 0xffff;
                Map<Long, ObjectInfo> target = tag == DT_SCE_MODULE_ATTR ? modules : libraries;
                target.computeIfAbsent(id, ignored -> new ObjectInfo()).attributes = value & 0xffffffffffffL;
            }
        }

        private void parseSymbol(long address) throws Exception {
            Address symbol = address(address);
            int nameOffset = (int) u32(symbol);
            int info = program.getMemory().getByte(symbol.add(4)) & 0xff;
            int shndx = u16(symbol.add(6));
            long value = q64(symbol.add(8));
            long size = q64(symbol.add(16));
            if (shndx == 0 || (info & 0xf) != 2 && (info & 0xf) != 1 || nameOffset == 0) return;
            String encoded = stringAt(strtab + nameOffset);
            String name = decodeSymbolName(encoded, info & 0xf);
            if (name == null || value == 0) return;
            label(value, name, "PS5 symbol: " + encoded);
            if ((info & 0xf) == 2 && size > 0 && functions.add(value)) {
                FunctionManager manager = program.getFunctionManager();
                if (manager.getFunctionAt(address(value)) == null) {
                    manager.createFunction(name, address(value), new AddressSet(address(value), address(value + size - 1)), SourceType.IMPORTED);
                }
            }
        }

        private String decodeSymbolName(String encoded, int type) {
            String[] parts = encoded.split("#", -1);
            if (parts.length != 3) return encoded;
            long nid = decode(parts[0]);
            long library = decode(parts[1]);
            long module = decode(parts[2]);
            ObjectInfo mod = modules.get(module);
            ObjectInfo lib = libraries.get(library);
            if (mod == null || lib == null) return encoded;
            String result = knownNids.get(nid);
            if (result == null) result = String.format("nid%s_%s_%s_0x%016x", type == 2 ? "f" : "o", mod.name, lib.name, nid);
            return result;
        }

        private void label(long value, String name, String comment) throws Exception {
            Address target = address(value);
            program.getSymbolTable().createLabel(target, name, SourceType.IMPORTED);
            addComment(value, comment);
        }

        private void addComment(long value, String comment) throws Exception {
            addComment(address(value), comment);
        }

        private void addComment(Address target, String comment) throws Exception {
            if (program.getMemory().contains(target)) program.getListing().setComment(target, CodeUnit.PRE_COMMENT, comment);
        }

        private String stringAt(long value) throws Exception {
            Address target = address(value);
            StringBuilder result = new StringBuilder();
            for (int i = 0; i < 0x10000 && program.getMemory().contains(target.add(i)); i++) {
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

    private static final class ObjectInfo {
        String name = "unknown";
        String version = "0.0";
        long attributes;
        boolean export;
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