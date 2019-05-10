open util
module ptx

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun com : MemoryEvent->MemoryEvent { rf + ^co + fr }
fun rfi : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe : MemoryEvent->MemoryEvent { rf - rfi }

fun same_thread [rel: Event->Event] : Event->Event { rel & (iden + ^po + ~^po) }
fun location[rel: Event->Event] : Event->Event { rel & (address.~address) }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Model of memory=

sig Address { } { #(address :> this) > 1 and #(Write <: address :> this) > 0 }

sig Scope { subscope: set Scope }
fun System : Scope { Scope - Scope.subscope }
fact one_system { one System }
sig Thread extends Scope { start: one Event }

abstract sig Event {
  po: lone Event, 
  scope: one Scope
}
abstract sig Fence extends Event { } { some (Scope-Thread) => scope not in Thread }
abstract sig MemoryEvent extends Event {
  address: one Address,
  observation: set MemoryEvent,
}
sig Read extends MemoryEvent {
  rmw: lone Write,
  dep: set Event
}
sig Write extends MemoryEvent {
  rf: set Read,
  co: set Write,
}

//address
fact com_addr { co + rf + fr in address.~address }

//po
fact po_acyclic { acyclic[po] }
fact some_thread { all e: Event | one t: Thread | t->e in start.*po }
fun po_loc : Event->Event { ^po & address.~address }

//reads
fact lone_source_write { rf.~rf in iden }
fun fr : Read->Write {
  ~rf.^co
  +
  // also include reads that read from the initial state
  ((Read - (Write.rf)) <: (address.~address) :> Write)
}

//dep
fact dep_facts { dep in ^po }
//rmws
fact rmw_facts { rmw in po & dep & address.~address & scope.~scope }
//scope
fact inv_subscope { subscope.~subscope in iden }
fact thread_subscope { no Thread.subscope }
fact subscope_acyclic { acyclic[subscope] }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =PTX=

pred no_thin_air { acyclic[rf + dep] }
pred location_sc { acyclic[strong[com] + po_loc] }
pred atomicity   { no strong[fr].(strong[co]) & rmw }
pred coherence   { location[Write <: cause :> Write] in ^co }
pred causality   { irreflexive[optional[fr + rf].cause] }
pred ptx_mm {
  no_thin_air and location_sc and atomicity and coherence
  and causality
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Auxiliaries=

fact obs_in_rf_rmw { observation in ^(strong[rf] + rmw) }
fact rf_obs { strong[rf] in observation }
fact rmw_obs { observation.rmw.observation in observation }

fun prefix : Event->Event      { (Release <: optional[po_loc] :> Write) + (FenceRels <: ^po :> Write) }
fun suffix : Event->Event      { (Read <: optional[po_loc] :> Acquire) + (Read <: ^po :> FenceAcqs) }
fun Releasers : Event          { Release + FenceRels + (FenceRels.po.rmw)}
fun Acquirers : Event          { Acquire + FenceAcqs }
fun sync[head: Event, tail: Event] : Event->Event {
  head <: strong[prefix.^observation.suffix] :> tail
}
fun cause_base : Event->Event  {
  ^(*po.(synchronizes + sc + sync[Releasers,Acquirers]).*po)
}
fun cause : Event->Event {
  cause_base + (observation.(po_loc + cause_base))
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////

fun typed[rel: Event->Event, type: Event] : Event->Event {
  type <: rel :> type
}
fun inside[s: Scope] : Event {
  s.*subscope.start.*po
}
fun scoped[s: Scope] : Event {
  s.*~subscope.~scope
}
fun strong_r : Event->Event {
  symmetric[scope.*subscope.start.*po]
}
fun weak[r: Event->Event]: Event->Event {
  r - strong_r
}
fun strong[r: Event->Event]: Event->Event {
  r & strong_r
}
pred is_strong[r: Event->Event] {
  r in strong_r
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////

sig FenceAcq extends Fence { }
sig FenceRel extends Fence { }
sig FenceAcqRel extends Fence { }
sig FenceSC extends FenceAcqRel {
  sc: set FenceSC,
}

fun FenceRels : Fence { FenceAcqRel + FenceRel + BarrierWait }
fun FenceAcqs : Fence { FenceAcqRel + FenceAcq + BarrierWait }

sig Acquire extends Read { } { scope not in Thread }
sig Release extends Write { } { scope not in Thread }

//writes
fact co_per_scope {
  all a: Address | all s: Scope |
    total[co, scoped[s] & inside[s] & (a.~address & Write)]
}
abstract sig Barrier extends Event {} { }
sig BarrierArrive extends Barrier { synchronizes: set BarrierWait }
sig BarrierWait extends Barrier {}

//scope
fact scope_inclusion { scope in *~po.~start.*~subscope }

//barrier
// no isolated barrier pieces
fact { all b: BarrierArrive | some b.synchronizes }
fact { all b: BarrierWait | some b.~synchronizes }
// bar.sync = BarrierArrive; po; BarrierWait
fact { BarrierWait in BarrierArrive.(po & synchronizes) }
// transitivity
fact { synchronizes.~synchronizes.synchronizes in synchronizes }
fact { ~synchronizes.synchronizes.~synchronizes in ~synchronizes }
// Prevents two BarrierArrives in the same thread synchronizing with the same Barrier
fact { no ^po & synchronizes.~synchronizes }
// Prevents one BarrierArrive from synchronizing with two BarrierSyncs in the same thread
fact { no ^po & ~synchronizes.synchronizes }
// synchronizes is morally strong: i.e., you can only synchronize within the same block
fact { is_strong[synchronizes] }

//fence
fact wf_sc {
  //all s: Scope | total[sc, scoped[s] & inside[s] & FenceSC]
  all disj f1, f2 : FenceSC | f1->f2 in strong_r => (f1->f2 in sc or f2->f1 in sc)
  sc in typed[strong_r, FenceSC]
  acyclic[sc]
}
