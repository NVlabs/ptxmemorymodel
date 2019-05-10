module compile_src11_ptx
open util as util
open ptx as hw
open src11[hw/Event,hw/Address,hw/Scope] as sw

////////////////////////////////////////////////////////////////////////////////

pred wf_map_insts {
  // All HW insts are derived from some SW inst
  sw/Event.map = hw/Event
  // every sw event lowers to at least one hw event
  all e: sw/Event | some e.map
  // every hw event comes from exactly one sw event
  all e: hw/Event | one e.~map
  // map sb onto po
  sb in map.^po.~map
}

pred wf_map_addrs {
  /*   sw/Event ---address->  sw/Address
   *      |                        |
   *     map                    addrmap
   *      |                        |
   *      V                        V
   *   hw/Event --address-->  hw/Address
   */
  // "map" respects the address mappings
  sw/MemoryEvent<:address = map.(hw/MemoryEvent<:address).(~addrmap)
}

pred wf_map_scope {
  scopemap.~scopemap in iden
}

pred wf_map {
  wf_map_insts
  wf_map_addrs
  wf_map_scope
}

pred reverse_map_rf {
  hw/Write <: rf in ~map.(sw/Write <: rf).map
  hw/Read - hw/Write.rf = map[sw/Read - sw/Write.rf]
}

pred reverse_map_co {
  co in ~map.mo.map
}

pred reverse_map_fr {
  hw/fr in ~map.rb.map
}

pred reverse_map {
  reverse_map_rf
  reverse_map_co
  reverse_map_fr
}

////////////////////////////////////////////////////////////////////////////////

pred compile_read_na  { (sw/Read  & NA ).map in hw/Read }
pred compile_read_rx  { (sw/Read  & RLX).map in hw/Read }
pred compile_read_aq  { (sw/Read  & ACQ).map in hw/Acquire }
pred compile_write_na { (sw/Write & NA ).map in hw/Write }
pred compile_write_rx { (sw/Write & RLX).map in hw/Write }
pred compile_write_rl { (sw/Write & REL).map in hw/Release }
pred compile_fence_aq { (sw/Fence & ACQ).map in hw/FenceAcq }
pred compile_fence_rl { (sw/Fence & REL).map in hw/FenceRel }
pred compile_fence_ar { (sw/Fence & AR ).map in hw/FenceAcqRel }
pred compile_fence_sc { (sw/Fence & SC ).map in hw/FenceSC }

pred compile_rmw { sw/Read <: rmw = map.rmw.~map }

pred compile_scope {
  (sw/Thread <: start).map = scopemap.start
  (sw/Event <: scope).scopemap = map.scope
  (sw/Scope <: subscope).scopemap in scopemap.subscope
}

pred compile_MemoryEvents {
  compile_read_na
  compile_read_rx
  compile_read_aq
  compile_write_na
  compile_write_rx
  compile_write_rl
  compile_write_na
  compile_fence_aq
  compile_fence_rl
  compile_fence_ar
  compile_fence_sc
  compile_rmw
  compile_scope
}

pred compile_src11_ptx {
  // Start with a valid C11 program
  not racy

  // ...compile onto ptx
  wf_map
  compile_MemoryEvents

  // ...find a legal ptx execution
  ptx_mm

  // ...reverse-map that execution back into C11
  and reverse_map
}
assert compile_src11_ptx_legal { compile_src11_ptx => src11 }
check compile_src11_ptx_legal for 6 but 4 sw/Event

assert compile_src11_ptx_nonta_legal {
  compile_src11_ptx => sw/coherence and sw/atomicity and sw/sc
}
check compile_src11_ptx_nonta_legal for 4

////////////////////////////////////////////////////////////////////////////////

run sanity {
  some hw/Read
  compile_src11_ptx
} for 4 but 4 hw/Scope

////////////////////////////////////////////////////////////////////////////////

assert src11_ptx_legal_coherence { compile_src11_ptx => sw/coherence }
check src11_ptx_legal_coherence for 6

assert src11_ptx_legal_atomicity { compile_src11_ptx => sw/atomicity }
check src11_ptx_legal_atomicity for 6

assert src11_ptx_legal_sc { compile_src11_ptx => sw/sc }
check src11_ptx_legal_sc for 6 but 5 sw/Event

assert src11_ptx_legal_no_thin_air { compile_src11_ptx => sw/no_thin_air }
check src11_ptx_legal_no_thin_air for 6

////////////////////////////////////////////////////////////////////////////////
// Lemmas

fun syncacqrel : hw/Event->hw/Event { *po.(sync[Releasers, Acquirers]).*po }

assert sb_syncacqrel {
  compile_src11_ptx =>
  sb in map.^po.~map
}
check sb_syncacqrel for 7 but 4 sw/Event
  
assert sw_syncacqrel {
  compile_src11_ptx =>
  strong[sw] in map.syncacqrel.~map
}
check sw_syncacqrel for 7 but 4 sw/Event
  
assert hb_syncacqrel {
  compile_src11_ptx =>
  hb in map.(^po + ^syncacqrel).~map
}
check hb_syncacqrel for 7 but 4 sw/Event

assert psc_F {
  compile_src11_ptx =>
  psc in (optional[hb]).(hb+eco).(optional[hb])
}
check psc_F for 7 but 4 sw/Event

// Sanity checks

run MP { some NA <: sb.sw.sb :> NA & rf and some sw/Scope <: subscope and compile_src11_ptx and src11 } for 4

run sm { compile_src11_ptx and some scopemap.~scopemap - iden } for 4
