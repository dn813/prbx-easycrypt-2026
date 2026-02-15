require import AllCore List Bool Ring IntDiv.
require (****) Group.

clone Group.CyclicGroup as G.

axiom prime_p : prime G.order.
  
clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

import G GP.

theory LRSTypes.
  type pkey = group. (* public encryption key *)
  type skey = exp. (* private encryption key *)
  type tag = group.
  type pcred = group * group. (* public credential/signature *)
  type scred = exp * exp * exp. (* private credential/signature *)
  type sig = exp * exp list * exp list * exp list * tag. (* Signature *)
  type generator = group. (* Group generator *)
  type ring.

  type string = pcred list * tag * group * group * group * group.
  type event = string.

  type ptxt = group. (* Plaintext *)

  op H_G: string -> group.
  op H_q: string -> exp.

  op ( * ): exp -> exp -> exp.
  op ( - ): exp -> exp -> exp.

  op [lossless uniform full] dgroup: group distr.
  op [lossless uniform full] dexp: exp distr.
  
  op enc (pk: pkey) (m: group, r: exp) = (g ^ r, m * (pk ^ r)). (* enc() *)
end LRSTypes.
export LRSTypes.  
  
module type LinkableRingSS = {
  proc setup(): generator * generator * (string -> group) * (string -> exp) * pkey
  proc kgen(): pcred * scred
  proc sign(L: pcred list, ev: event, sc: scred, m: ptxt): sig
  proc verify(L: ring, ev: event, m: ptxt, s: sig): bool
  proc link(s1: sig, s2: sig): bool
}.

module LRS : LinkableRingSS = {
  var g, h: generator
  var pk: pkey
  proc setup(): generator * generator * (string -> group) * (string -> exp) * pkey = {
    var sk: skey;

    g <$ dgroup;
    h <$ dgroup;

    sk <$ dexp;
    pk <- g ^ sk;
    
    return (g, h, H_G, H_q, pk);
  }
  
  proc kgen(): pcred * scred = {
    var x, y, r: exp;
    var sc: scred;
    var pc: pcred;
    x <$ dexp;
    y <$ dexp;
    r <$ dexp;
    sc <- (x, y, r);

    pc <- enc(pk) (g ^ x * h ^ y) (r);
    return (pc, sc);
  }

  proc sign(L: pcred list, ev: event, sc_i: scred, m: ptxt): sig = {
    var e: group;
    var t: tag;
 
    var xi, yi, ri;
    var alp, bet, gam, c, c1;
    var ki, ki', ki'';
    var i: int;
    var j: int;

    var cred_j: pcred;
    var cred_j1, cred_j2: group;
    var default_pcred;
    var kj, kj', kj'';

    var sj, tj, pj: exp;
    var si, ti, pi: exp;
    var ss, ts, ps: exp list;
    
    xi <- sc_i .` 1;
    yi <- sc_i .` 2;
    ri <- sc_i .` 3;

    e <- H_G(ev);
    t <- e ^ xi;
    
    alp <$ dexp;
    bet <$ dexp;
    gam <$ dexp;

    ki <- g ^ alp * h ^ gam * pk ^ bet;
    ki' <- g ^ bet;
    ki'' <- e ^ alp;
    c <- H_q(L, t, ki, ki', ki'', m);

    j <- i + 1;
    while (j <> i) {
      if (j = 1) {c1 <- c;}
      cred_j <- nth default_pcred L j;
      cred_j1 <- cred_j .` 1;
      cred_j2 <- cred_j .` 2;
        
      sj <$ dexp;
      tj <$ dexp;
      pj <$ dexp;
      if (i < j) {
        ss <- ss ++ [sj];
        ts <- ts ++ [tj];
        ps <- ps ++ [pj];
      }
      else {
        ss <- [sj] ++ ss;
        ts <- [tj] ++ ts;
        ps <- [pj] ++ ps;
      }
      
      kj <- g ^ tj * h ^ pj * pk ^ sj * cred_j2 ^ c;          kj' <- g ^ sj * cred_j1 ^ c;
      kj'' <- e ^ tj * t ^ c;
      c <- H_q(L, t, kj, kj', kj'', m);
      j <- j + 1;
      if (j = size(L) + 1) {j <- 1;}
    }
    si <- bet - (c * ri);
    ti <- alp - (c * xi);
    pi <- gam - (c * yi);
    ss <- ss ++ [si];
    ts <- ts ++ [ti];
    ps <- ps ++ [pi];
    
    return (c1, ss, ts, ps, t);
  }

  proc verify(L: pcred list, ev: event, m: ptxt, sig: sig): bool = {
    var e, v: group;
    var j: int;
    var result;

    var kj, kj', kj'';
    
    e <- H_G(ev);
    j <- 1;
    while (j < size(L)) {
      kj <- g ^ tj * h ^ pj * pk ^ sj * cred_j2 ^ c;
      kj' <- g ^ sj * cred_j1 ^ c;
      kj'' <- e ^ tj * t ^ c;
      c <- H_q(L, t, kj, kj', kj'', v);
    }
  }
}.
