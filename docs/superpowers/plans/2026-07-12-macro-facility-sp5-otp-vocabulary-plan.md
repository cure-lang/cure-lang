# SP5 OTP Vocabulary and Pure Module Values

## Goal

Land the closed OTP behaviour/callback vocabulary and a pure `lift module`
value representation before any runtime container integration.

## Scope

- Validate callback names and arities against the four closed OTP behaviours.
- Expose callback signatures for macro elaborators.
- Mint a serializable module value containing the requested name, behaviour,
  callbacks, and declarations without compiling or loading code.

## Invariants

- Unknown behaviours, callbacks, and arities are rejected explicitly.
- `lift_module` is pure and append-only; it does not call `Code.compile` or
  load a BEAM module.
- No trusted Core changes and no runtime OTP side effects.

## Verification

- Positive and negative callback vocabulary checks for each behaviour.
- A valid supervisor module value is produced with declaration order intact.
- Invalid callback input is rejected before minting.

