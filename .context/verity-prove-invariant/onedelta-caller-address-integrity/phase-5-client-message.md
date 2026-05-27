# Phase 5 - Client Message

Hi team,

Good news: we modeled and formally verified an invariant on the scoped OneDeltaComposerEthereum caller-address fund-pull paths in Verity.

The proof shows that every modeled ERC20, Permit2, flash-callback, swap-callback, and V3 direct callback pull uses the original `deltaCompose` caller as the source address. In simpler terms: if one of these modeled pulls succeeds, it cannot charge an intermediate callback, pool, or embedded calldata address instead of the user who started the batch.

Full write-up here:
https://lfglabs.dev/research/onedelta-caller-address-integrity

Happy to answer questions or explore extending formal verification coverage across the rest of 1delta.
