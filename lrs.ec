require import AllCore List Bool.

type key.
type ring.
type sig.
type event.
type msg.
type cip.
type bb.
type cnd = int.
type cndlist = [
  | Nil
  | Cons of cnd
].
type voter = int.
type ballot.
type piproof.
type result.

module type LRS = {
  proc setup(): key
  proc kgen(): key * key
  proc sign(L: ring, ev: event, sc: key, m: msg): sig
  proc verify(L: ring, ev: event, m: msg, s: sig): bool
  proc link(s1: sig, s2: sig): bool
}.
