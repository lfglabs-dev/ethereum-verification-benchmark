# Zodiac Roles v3 Decoder Faithfulness

This benchmark targets the Roles v3 ABI decoder in Gnosis Guild's
`zodiac-modifier-roles` repository, branch `contracts-v3`, commit
`172723b165d482c5565e413e9927604b0dc168b6`.

The invariant is decoder faithfulness: for a scoped function ABI type tree and a
leaf parameter path, the byte region isolated by the Roles v3 lazy decoder
matches the region selected by an independent canonical Solidity ABI v2 layout
model. The reference model is not built from Roles' `AbiLocation.children`,
`AbiLocation.size`, or `Topology` metadata. It models ABI HEAD/TAIL layout,
block-relative offsets, 4-byte selector skip, length words for dynamic payloads,
dynamic-array element blocks, and `ceil32` padding.

The reference is a hand-written in-repository ABI layout model, not an external
ABI oracle. Its value is that the Roles-shaped model and the ABI-shaped model
were transcribed from different sources and then proved to agree; the proof does
not eliminate shared transcription error by itself.

Tuple and dynamic-array value regions are full encoded regions. Dynamic tuple
children contribute their offset word plus tail payload, and dynamic arrays
contribute the length word plus every encoded element.

The proved public obligations are:

- `metadata_bridge`: `rolesIsInlined t = abiStatic t`, and Roles inline size
  equals ABI static byte size.
- `roles_decoder_faithful`: Roles and the independent ABI reference isolate the
  same leaf byte region.
- `roles_decoder_bounds_safe`: every successful Roles extraction result lies
  inside calldata; malformed reads and non-forward/out-of-range offsets return
  overflow.
- `canonical_injectivity`: if reference regions agree, governed Roles regions
  agree. This is a congruence corollary of faithfulness, not keccak or calldata
  injectivity.

Terminal condition: `PROOF`.

Trusted assumptions outside the Lean theorem:

- `Integrity.enforce` plus ConditionPacker/Unpacker yields a well-formed type
  tree with metadata equal to `rolesIsInlined` and `rolesInlinedSize`.
- Calldata canonicality is the premise for the faithfulness interpretation; the
  bounds theorem covers adversarial malformed calldata at the modeled extraction
  boundary.
- Keccak256 injectivity is needed only when applying the decoder result to
  `size > 32` hash-comparison paths.
- Big-endian shift/mask identities match Solidity's sub-word slicing paths.
- Fuel bounds are part of the model: encoded-size computation uses a 256-step
  bound and navigation uses `path.length + 64`; deeper wrapper trees conservatively
  return overflow.
- `staticWords n` is word-granular, and `transparent` covers the single-child
  logical `Encoding.None` wrapper.

Out of scope: `Operator.Custom`, `Zip`, `Slice`, `Pluck`,
`MultiSendUnwrapper`, condition-consumption state, comparison operators, and
external calls.
