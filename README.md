# Ghidra PS5 ELF analyzer

This is the Ghidra 12.1.3 port of the PS5 ELF post-loader functionality. Ghidra's
built-in ELF loader remains responsible for mapping segments and applying normal
ELF relocations. `Ps5ElfAnalyzer` adds PS5-specific dynamic metadata and symbol
names after loading.

## Install

1. Set `GHIDRA_INSTALL_DIR` to the Ghidra 12.1.3 installation directory in
   `gradle.properties` or the environment.
2. Run `gradlew.bat buildExtension` from a Gradle wrapper-enabled checkout, or
   run the equivalent Gradle command with the Gradle distribution bundled with
   your Ghidra setup. The existing `cfg/ps5_symbols.txt` is packaged directly.
3. In Ghidra, use **File > Install Extensions** and select the generated ZIP.

The extension is installed as `ps5-elf-analyzer`. The analyzer is enabled by default for little-endian x86-64 PS5 executables
(`ET_SCE_EXEC_ASLR`) and PRX files (`ET_SCE_DYNAMIC`). It emits PS5 module and
library information as program metadata and applies decoded exports and defined
symbols as labels and functions.
