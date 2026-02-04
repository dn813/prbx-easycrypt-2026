require import AllCore List Bool Group Ring IntDiv.

type pkey. (* public encryption key *)
type skey = int. (* private encryption key *)
type pcred. (* public credential/signature *)
type scred. (* private credential/signature *)
type sig. (* Signature *)
type group.
type group_elem = int.
type generator = group_elem. (* Group generator *)
type ring.
type event.

type ptxt. (* Plaintext *)
type ctxt. (* Ciphertext *)
type string.

clone Group.CyclicGroup as G with
  type group <- group. (* group with prime order *)

axiom prime_p: prime G.order.

op H_G: string -> group.
op H_q: string -> int.
op [lossless uniform full] dgroup: group_elem distr.
op [lossless uniform full] dskey: skey distr.

op (^) 

module type LinkableRingSS = {
  proc setup(): generator * generator * pkey
  proc kgen(): pcred * scred
  proc sign(L: ring, ev: event, sc: scred, m: ptxt): sig
  proc verify(L: ring, ev: event, m: ptxt, s: sig): bool
  proc link(s1: sig, s2: sig): bool
}.

module LRS : LinkableRingSS = {
  proc setup(): generator * generator * pkey = {
    var g, h: generator;
    var sk: skey;
    var pk: pkey;

    g <$ dgroup;
    h <$ dgroup;

    sk <$ dskey;
    pk <- g ^ sk;
    
    return g * h * pk;
  }
  
  (* proc kgen(): pc * sc = {
    var x, y, r: int;
    var sc: sc;
    var pc: pc;
    x <$ dint;
    y <$ dint;
    r <$ dint;
    sc <- 
    var pc: pc;
    x <$ dint;
    y <$ dint;
    r <$ dint;
    sc <- x * y * r;
  } *)
}.
