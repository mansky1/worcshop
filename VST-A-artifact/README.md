This is the artifact of paper **VST-A: A Foundationally Sound Annotation Verifier**

Building instructions:

Notes: The building can be sped up by proving job parameters to `make`. But it is recommended not to allow too many jobs in parallel (like simply `make -j`) to avoid OOM killing. For estimation of job limit, each job may have around 1GB peak memory usage.

1. Install OPAM package manager, following instructions in [https://opam.ocaml.org/doc/Install.html](https://opam.ocaml.org/doc/Install.html)

2. Install OCaml 4.10.2, Menhir 20190924 and Coq 8.12.2
   ```bash
   $ opam install ocaml.4.10.2 menhir.20190924 coq.8.12.2
   ```

3. Build patched VST 2.5 in directory `VST-patch/`. Run `make` in its directory.

4. Build CompCert-A in directory `compcert-for-vsta/` for the frontend. In its directory, run
   ```bash
   $ sh configure x86_32-linux -clightgen -aclightgen -ignore-coq-version -no-runtime-lib
   $ make
   ```

5. Build SetsClass in directory `sets/` for some examples. Run `make` in its directory.

6. In VST-A/, run `make`, the following will be built
   - the split function and its soundness proof in `csplit/`
   - the proof automation tactics in `floyd-seq/`
   - the parsed results and proofs of test programs in `cprogs/`

List of claims:

1. The Coq implementation of split function is in file `VST-A/csplit/AClight.v`

2. The OCaml implementation of split function is in directory `compcert-for-vsta/exportaclight`

3. The soundness of split function is theorem `soundness` in file `VST-A/csplit/soundness.v`

4. The annotated C programs and correctness proofs used in evaluation are located in directory `VST-A/cprogs`, for example:

   - `VST-A/cprogs/dlist.c` is the source code of annotated C program defining some C functions on doubly linked lists and their specifications

   - in directory `VST-A/cprogs/dlist`, file `program.v` and `annotation.v` are the generated Coq definitions of annotated C program. File `definitions.v` contains the Coq definitions, lemmas and tactics used in annotations and proofs of `VST-A/cprogs/dlist.c`

   - in directory `VST-A/cprogs/dlist`, directory `append`, `reverse`, `dequeue` and `enqueue` contain the straightline Hoare triples and proofs of corresponding functions in `VST-A/cprogs/dlist.c`. Specifically, file `verif.v` in each directory is the overall functional correctness proof of each function.
