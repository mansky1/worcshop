Our modification of VST has two parts
- we prove some model level lemmas on preciseness of load/store (required to derive the conjunction rule)
- we define a stronger `semax` for VST-A, that removes bupd and restricts function specification being called to be precise

## Key Definitions & Lemmas of the stronger program logic

- `model_lemmas.v`: 
  - model level lemmas for precise read/write
    - `mapsto_join_andp_det`
    - `mapsto_join_andp_write_det`
  - `precise_funspec`: definition of precise function specification
  - two rewriting lemmas for function call (written in model level to make use of fash/unfash conveniently)
    - `func_at_unique_rewrite`:
      - rewrite `func_at` : `func_at (A P1 Q1) addr & func_at (A P2 Q2) addr |-- P1 x * (Q1 x -* R) <-> P2 x * (Q2 x -* R)`
    - `funspec_rewrite`:
      - rewrite state with subsumption: `gA gP gQ <: A P Q & P x * (Q x -* R) |-- EX x', gP x' * (gQ x' -* R)`
  
- `logic_lemmas.v`: 
  - transfer lemmas in `model_lemmas.v` to logic scope
  
- `strong.v`
  - definition of precise function specification in logic scope (identical to `model_lemmas.v`)
  - `semax`: our stronger program logic
  - inversion lemmas
  - `semax_noXXX_inv`: noreturn/nocontinue/nobreak lemmas
  - `semax_conj_rule`: conjunction rule
  - `aux_semax_extract_exists`
  - `semax_derives`: soundness w.r.t. VST's program logic
