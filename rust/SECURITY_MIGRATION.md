# Prover memory-hygiene migration

The verifier-only default and zeroizing prover APIs are a deliberate breaking
security release for `runtime-algebra`, `runtime-ligero`, `runtime-sumcheck`,
and `runtime-zk`. Their package versions move from 0.1.0 to 0.2.0.

- Enable each crate's `prover` feature when proving is required.
- Add `Zeroize` bounds to generic prover element types.
- Runtime field implementations must make `RuntimeField::Accum` implement
  `Zeroize`; sumcheck now wipes witness-derived accumulators on every exit.
- Treat `eval_circuit` and `eval_quad` results as zeroizing containers.
  Existing indexing and iteration continue through `Deref`; avoid converting
  them back into ordinary `Vec` values.
- Pass either an existing `Vec<Vec<E>>` or the zeroizing
  `WitnessLayers<E>` directly to `prove` and `prove_core`.
- Treat `SumcheckProofAux::bound_quad` as a `ZeroizingVec`. Indexing,
  iteration, and mutation remain available through `Deref` and `DerefMut`.
- Add `Zeroize` to element bounds used with `Tableau::new` and
  `ZkCommitResult`. These public types now wipe prover-owned values on drop.

Verifier-only callers require no migration beyond leaving the `prover`
feature disabled.
