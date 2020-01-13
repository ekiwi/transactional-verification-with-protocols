# Makai Mann Btor2 Benchmarks

These are some benchmarks from Makai Mann at Stanford from
his [TACAS'20 submission](https://github.com/makaimann/tacas2020-exps).

Some of the same files seem to also have been used for the `hwmcc19`
and we are trying to recreate some of these configurations here.

**TODO**: We should check with Makai before including any results
in a paper to make sure we are checking something that is comparable to
the `hwmcc19` benchmarks.

Some unsolved configurations at `hwmcc19` are:

```
arbitrated_top_n2_w128_d64_e0
arbitrated_top_n2_w32_d128_e0
arbitrated_top_n2_w64_d128_e0
arbitrated_top_n2_w8_d128_e0
arbitrated_top_n3_w128_d128_e0
arbitrated_top_n3_w16_d64_e0
arbitrated_top_n3_w64_d128_e0
arbitrated_top_n3_w8_d128_e0
arbitrated_top_n4_w64_d128_e0
arbitrated_top_n5_w16_d128_e0
arbitrated_top_n5_w64_d128_e0
arbitrated_top_n5_w64_d64_e0
arbitrated_top_n5_w8_d128_e0
circular_pointer_top_w128_d128_e0
circular_pointer_top_w16_d64_e0
circular_pointer_top_w32_d128_e0
circular_pointer_top_w64_d64_e0
circular_pointer_top_w8_d128_e0
circular_pointer_top_w8_d64_e0
shift_register_top_w128_d64_e0
shift_register_top_w32_d128_e0
shift_register_top_w64_d128_e0
shift_register_top_w64_d64_e0
```
**IMPORTANT**: there are more solved configurations!
E.g. `abc.superprove` solved one `d=128` configuration
of the `shift` fifo.


Solved configurations include:
```
arbitrated_top_n2_w128_d16_e0
arbitrated_top_n2_w16_d16_e0
arbitrated_top_n2_w16_d32_e0
arbitrated_top_n3_w16_d16_e0
arbitrated_top_n3_w32_d16_e0
arbitrated_top_n3_w32_d32_e0
arbitrated_top_n4_w128_d16_e0
arbitrated_top_n4_w32_d16_e0
arbitrated_top_n5_w128_d16_e0
arbitrated_top_n5_w16_d32_e0
arbitrated_top_n5_w32_d32_e0
arbitrated_top_n5_w8_d32_e0
circular_pointer_top_w16_d16_e0
circular_pointer_top_w32_d16_e0
circular_pointer_top_w8_d32_e0
shift_register_top_w32_d8_e0
shift_register_top_w64_d8_e0
```
