# Vendored copy note: only the ARMv8 assembly (cake_lpr_arm8.S) is vendored
# here, so the default target builds that. The x64 cake_lpr.S is not vendored;
# fetch it from upstream (https://github.com/tanyongkiam/cake_lpr) to use the
# x64 or starexec targets.

# Default build for native ARMv8 (replace gcc with your compiler)
cake_lpr_arm8: basis_ffi.c cake_lpr_arm8.S
	gcc basis_ffi.c cake_lpr_arm8.S -o cake_lpr -std=c99

# Build for x64 (requires the non-vendored cake_lpr.S from upstream)
cake_lpr: basis_ffi.c cake_lpr.S
	gcc -O2 basis_ffi.c cake_lpr.S -o cake_lpr -std=c99

# armv8 version (emulation on x64)
#cake_lpr_arm8_emu: basis_ffi.c cake_lpr_arm8.S
#	aarch64-linux-gnu-gcc -static basis_ffi.c cake_lpr_arm8.S -o cake_lpr_arm8

# x64 build with 64 GB heap and 16 GB stack for starexec
starexec: basis_ffi.c cake_lpr.S
	gcc basis_ffi.c cake_lpr.S -o cake_lpr -std=c99 \
	-DCML_HEAP_SIZE=65536 -DCML_STACK_SIZE=16384

clean:
	rm -fv cake_lpr cake_lpr_arm8
