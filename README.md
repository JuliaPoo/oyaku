# Oyaku

## Setup

### Clone project

```
git clone https://github.com/JuliaPoo/oyaku
cd oyaku
git submodule update --recursive --init --remote
```

### Install dependencies

```
opam install coq.8.20.0
opam install sexplib

opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-mathcomp-ssreflect
opam install coq-mathcomp-analysis
```

### Build egg

```
cd submodules/egg
cargo build --release --bin coquetier
```

### Build egg-tactic:

```
cd submodules/sponge
```

Open `src/egg_tactic.ml` and modify `egg_repo_path` accordingly.

```
make 
make install 
```

### Build Oyaku

(currently only runs Trig.v)

```
dune build
```
