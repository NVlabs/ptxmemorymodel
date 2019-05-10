module src11[hwEvent,hwAddress,hwScope]
open util

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Programs and candidate executions

sig Address {
  addrmap: one hwAddress
}
fun loc : Event->Event { address.~address }

sig Scope {
  subscope: set Scope,
  scopemap: one hwScope
}
fun System : Scope { Scope - Scope.subscope }
fact { one System }
sig Thread extends Scope { start: one Event }
fact scope_inclusion { scope in *~sb.~start.*~subscope }
fact { subscope.~subscope in iden }
fact { no Thread.subscope }
fact { acyclic[subscope] }
fact { no A.scope & Thread }
//fact { A.scope in System }
fact { NA.scope in Thread }

fact threads_unique { start.~start in iden }
fact events_in_threads { all e: Event | one e.*~sb.~start }

abstract sig MemoryOrder {}
one sig MemoryOrderNonAtomic extends MemoryOrder {}
one sig MemoryOrderRelaxed   extends MemoryOrder {}
one sig MemoryOrderAcquire   extends MemoryOrder {}
one sig MemoryOrderRelease   extends MemoryOrder {}
one sig MemoryOrderAcqRel    extends MemoryOrder {}
one sig MemoryOrderSeqCst    extends MemoryOrder {}

fun NA : set Event { MemoryOrderNonAtomic.ord }
fun RLX : set Event { MemoryOrderRelaxed.ord }
fun ACQ : set Event { MemoryOrderAcquire.ord }
fun REL : set Event { MemoryOrderRelease.ord }
fun AR : set Event { MemoryOrderAcqRel.ord }
fun SC : set Event { MemoryOrderSeqCst.ord }
fun A : Event { RLX + ACQ + REL + AR + SC }

fact WriteMO {
  all w: Write | w.memory_order in
  MemoryOrderNonAtomic + MemoryOrderRelaxed + MemoryOrderRelease
}
fact ReadMO {
  all r: Read | r.memory_order in
  MemoryOrderNonAtomic + MemoryOrderRelaxed + MemoryOrderAcquire
}
fact RMWMO {
  rmw in memory_order.(
    MemoryOrderRelaxed->MemoryOrderRelaxed +
    MemoryOrderAcquire->MemoryOrderRelaxed +
    MemoryOrderRelaxed->MemoryOrderRelease +
    MemoryOrderAcquire->MemoryOrderRelease +
    MemoryOrderSeqCst->MemoryOrderSeqCst
  ).~memory_order
}
fact FenceMO {
  all f: Fence | f.memory_order in
  MemoryOrderAcquire + MemoryOrderRelease + MemoryOrderAcqRel + MemoryOrderSeqCst
}

abstract sig Event {
  map: one hwEvent,
  sb: set Event,
  memory_order: one MemoryOrder,
  scope: one Scope
}
fun ord : MemoryOrder->Event { ~memory_order }
abstract sig MemoryEvent extends Event {
  address : one Address
}
sig Write extends MemoryEvent {
  rf: set Read,
  mo: set Write
}
sig Read extends MemoryEvent {
  rmw: lone Write
}
sig Fence extends Event {}

// com
fun rb : Read->Write {
  ~rf.mo
  +
  ((Read - Write.rf) <: address.~address :> Write) // for read-from-init reads
}
fact com_loc { rf + mo + rb in loc }

// sb
fact strict_partial_sb { strict_partial[sb] }

// reads
fact one_source_write { rf.~rf in iden }

// writes
fact strict_partial_mo { strict_partial[mo] }
fact mo_total_per_address { all a: Address | total[mo, a.~address :> Write] }

// rmw
fact rmw_sbimm {
  rmw in imm[sb] & loc
  sb.~rmw in sb
}

/*
fun psc : Event->Event {
  (ident[SC] + (ident[Fence & SC].hb))
  .(sb + eco + ((sb - loc).hb.(sb - loc)))
  .(ident[SC] + (hb.(ident[Fence & SC])))
}
*/

fun sbnl : Event->Event { sb - (sb & loc) }
fun scb : Event->Event { sb + sbnl + (hb.sbnl.hb) + mo + rb }
fun pscbase : Event->Event {
  (ident[SC] + (ident[Fence & SC].(optional[hb])))
  .scb
  .(ident[SC] + (optional[hb].(ident[Fence & SC])))
}
fun pscF : Event->Event {
  ident[Fence & SC].(hb + (hb.eco.hb)).(ident[Fence & SC])
}
fun psc : Event->Event {
  pscbase + pscF
}

////////////////////////////////////////////////////////////////////////////////
// Outcome

fun conflict : Event->Event {
  address.~address - iden - Read->Read
}

fun strong_r : Event->Event {
  symmetric[scope.*subscope.start.*sb]
}

fun strong[r: Event->Event]: Event->Event {
  r & strong_r
}

fun race : Event->Event { conflict - hb - ~hb }

pred racy { some race - strong_r }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Scoped RC11 model

fun rs : Event->Event {
  (ident[Write])
  .(optional[sb & loc])
  .(ident[Write & A])
  .*(strong[rf].rmw) // <--
}

fun sw : Event->Event {
  (ident[REL+AR+SC])
  .(optional[ident[Fence].sb])
  .rs.(strong[rf]) // <--
  .(ident[Read & A])
  .(optional[sb.(ident[Fence])])
  .(ident[ACQ+AR+SC])
}

fun hb : Event->Event { ^(sb + strong[sw]) }

fun com : Event->Event { rf + mo + rb }
fun eco : Event->Event { ^com }
assert ecos_equal { eco = (rf + mo + rb).(optional[rf]) }
check ecos_equal for 6

pred coherence   { irreflexive[hb.(optional[eco])] }
pred atomicity   { no rmw & rb.mo }
pred sc          { acyclic[strong[psc]] }
pred no_thin_air { acyclic[sb + rf] }

pred src11 {
  coherence
  atomicity
  sc
  no_thin_air
}
