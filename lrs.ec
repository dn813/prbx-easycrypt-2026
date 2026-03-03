require import AllCore List Bool IntDiv.
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
  proc sign(L: pcred list, ev: event, sc_i: scred, m: ptxt): sig
  proc verify(L: pcred list, ev: event, m: ptxt, s: sig): bool
  proc link(s1: sig, s2: sig): bool
}.

module LRS : LinkableRingSS = {
  var g, h: generator
  var pk: pkey
  var i: int
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
    var alp, bet, gam, c, c1, ci: exp;
    var ki, ki', ki'';
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
    (* Initially set c1 & ci to c, will be overwriten later *)
    c1 <- c;
    ci <- c;
    
    (* Initialise lists *)
    ss <- [];
    ts <- [];
    ps <- [];
    
    j <- 1;
    while (j < size(L) + 1) {
      if (j = 1) {c1 <- c;}
      if (j = i) {ci <- c;}
      cred_j <- nth default_pcred L j;
      cred_j1 <- cred_j .` 1;
      cred_j2 <- cred_j .` 2;
        
      sj <$ dexp;
      tj <$ dexp;
      pj <$ dexp;
      ss <- ss ++ [sj];
      ts <- ts ++ [tj];
      ps <- ps ++ [pj];
      
      kj <- g ^ tj * h ^ pj * pk ^ sj * cred_j2 ^ c;
      kj' <- g ^ sj * cred_j1 ^ c;
      kj'' <- e ^ tj * t ^ c;
      c <- H_q(L, t, kj, kj', kj'', m);
      j <- j + 1;
    }
    si <- bet - (ci * ri);
    ti <- alp - (ci * xi);
    pi <- gam - (ci * yi);
    ss <- put ss i si;
    ts <- put ts i ti;
    ps <- put ps i pi;
    
    return (c1, ss, ts, ps, t);
  }

  proc verify(L: pcred list, ev: event, m: ptxt, sig: sig): bool = {
    var c1, c: exp;
    var ss, ts, ps: exp list;
    var t: tag;
    
    var e: group;
    var j: int;
    var sj, tj, pj: exp;
    
    var cred_j: pcred;
    var cred_j1, cred_j2: group;
    var default_pcred;
    var kj, kj', kj'';

    var result: bool;
    result <- false;

    (* Initialise to random values *)
    sj <$ dexp;
    tj <$ dexp;
    pj <$ dexp;
    
    c1 <- sig .` 1;
    ss <- sig .` 2;
    ts <- sig .` 3;
    ps <- sig .` 4;
    t <- sig .` 5;
    e <- H_G(ev);
    
    j <- 1;
    c <- c1;
    while (j < size(L)) {
      cred_j <- nth default_pcred L j;
      cred_j1 <- cred_j .` 1;
      cred_j2 <- cred_j .` 2;

      kj <- g ^ tj * h ^ pj * pk ^ sj * cred_j2 ^ c;
      kj' <- g ^ sj * cred_j1 ^ c;
      kj'' <- e ^ tj * t ^ c;
      c <- H_q(L, t, kj, kj', kj'', m);
    }
    if(c1 = c) {result <- true;}
    return result;
  }

  proc link(s1: sig, s2: sig): bool = {
    (* Does not verify signautures, so this must be done at the call site *)
    var t1, t2;
    var result: bool <- false;
    t1 <- s1 .` 5;
    t2 <- s2 .` 5;
    if (t1 = t2) {result <- true;}
    return result;
  }
}.


module SignEquivalence = {
  proc sign(L: pcred list, ev: event, sc_i: scred, m: ptxt): sig = {
    var e: group;
    var t: tag;
 
    var xi, yi, ri;
    var alp, bet, gam, c, c1: exp;
    var ki, ki', ki'';
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

    ki <- LRS.g ^ alp * LRS.h ^ gam * LRS.pk ^ bet;
    ki' <- LRS.g ^ bet;
    ki'' <- e ^ alp;
    c <- H_q(L, t, ki, ki', ki'', m);
    (* Initially set c1 to c, will be overwriten later *)
    c1 <- c;
    
    (* Initialise lists *)
    ss <- [];
    ts <- [];
    ps <- [];
    
    j <- LRS.i + 1;
    while (j <> LRS.i) {
      if (j = 1) {c1 <- c;}
      cred_j <- nth default_pcred L j;
      cred_j1 <- cred_j .` 1;
      cred_j2 <- cred_j .` 2;
        
      sj <$ dexp;
      tj <$ dexp;
      pj <$ dexp;
      if (LRS.i < j) {
        (* Append to end of lists *)
        ss <- ss ++ [sj];
        ts <- ts ++ [tj];
        ps <- ps ++ [pj];
      }
      else {
        (* Insert values into position j *)
        ss <- insert sj ss j;
        ts <- insert tj ts j;
        ps <- insert pj ps j;
      }
      kj <- LRS.g ^ tj * LRS.h ^ pj * LRS.pk ^ sj * cred_j2 ^ c;
      kj' <- LRS.g ^ sj * cred_j1 ^ c;
      kj'' <- e ^ tj * t ^ c;
      c <- H_q(L, t, kj, kj', kj'', m);
      j <- j + 1;
      (* If reached n, set back to 1 *)
      if (j = size(L) + 1) {j <- 1;}
    }
    si <- bet - (c * ri);
    ti <- alp - (c * xi);
    pi <- gam - (c * yi);
    ss <- put ss LRS.i si;
    ts <- put ts LRS.i ti;
    ps <- put ps LRS.i pi;
    
    return (c1, ss, ts, ps, t);
  }
}.


lemma sign_equiv:
equiv [LRS.sign ~ SignEquivalence.sign : ={LRS.i, LRS.g, LRS.h, LRS.pk, L, ev, sc_i, m} ==> ={res}].
proof.
  proc.
  auto.
  seq 17 16: (={LRS.i, alp, bet, gam}).
  + auto.
  seq 1 1: (={LRS.i} /\ j{1} = 1 /\ j{2} = LRS.i{2} + 1); auto.
  + while (={LRS.i} /\ 0 < j{1} /\ 0 < j{2} /\ j{1} < size L{1} + 1 /\ j{2} < size L{1} + 1).
    + seq 1 1: (={LRS.i} /\ 0 < j{1} /\ 0 < j{2} /\ j{1} < size L{1} + 1 /\ j{2} < size L{1} + 1).
      + auto.
    + seq 
qed.
