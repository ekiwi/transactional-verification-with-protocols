# rocket

## PTW
The page table walker was extracted from a DefaultRV32Config of rocket-chip @ 1c9654c592a2ee8b7c5377de6061b1c516ebc3a6.

```
git clone https://github.com/ucb-bar/rocket-chip.git
cd rocket-chip
git checkout 1c9654c592a2ee8b7c5377de6061b1c516ebc3a6
git submodule update --init
cd vsim
make CONFIG=DefaultRV32Config verilog
```

Then extract the PTW module from `generated-src/freechips.rocketchip.system.DefaultRV32Config.v`
and save as `rtl/PTW.v`.
