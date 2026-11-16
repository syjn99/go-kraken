module
public import Kraken.AArch64.OmniSemantics

@[expose] public section

namespace Machine.Arm64

/-- Accept only deterministic effects with ordinary memory and aligned stack access. -/
def next? : Effects → Option MachineState
  | .done s => some s
  | .require_read_access _ _ k => next? (k ())
  | .require_write_access _ _ k => next? (k ())
  | .require_exec_access _ k => next? (k ())
  | _ => none

/-- A successful deterministic step satisfies the Kraken universal effect predicate. -/
theorem next_sound : ∀ (e : Effects) (t : MachineState), next? e = some t → e.All (· = t)
  | .done s, t, h => by cases h; rfl
  | .require_read_access _ _ k, t, h => next_sound (k ()) t h
  | .require_write_access _ _ k, t, h => next_sound (k ()) t h
  | .require_exec_access _ k, t, h => next_sound (k ()) t h
  | .unimplemented _, _, h => by cases h
  | .unaligned_sp _, _, h => by cases h
  | .nonmem_load .., _, h => by cases h
  | .nonmem_store .., _, h => by cases h
  | @Effects.undefined α inst k, _, h => by cases h

/-- Stop only at the requested address. Exhausted fuel and unsupported effects return none. -/
def run [Layout] (e : Executable) (ra : Int64) : Nat → MachineState → Option MachineState
  | 0, s => if s.pc = ra then some s else none
  | n + 1, s =>
    if s.pc = ra then some s
    else (next? (Executable.step e s .done)).bind (run e ra n)

/-- A successful bounded run proves termination in the Kraken machine model. -/
theorem run_sound [Layout] (e : Executable) (ra : Int64) (n : Nat) (s t : MachineState)
    (h : run e ra n s = some t) : Eventually (step1 e) (· = t) s := by
  induction n generalizing s with
  | zero =>
    simp only [run] at h
    split at h
    · cases h; exact .done _ rfl
    · cases h
  | succ n ih =>
    simp only [run] at h
    split at h
    · cases h; exact .done _ rfl
    · cases hn : next? (Executable.step e s .done) with
      | none => simp [hn] at h
      | some mid =>
        simp only [hn, Option.bind_some] at h
        refine .step s (· = mid) (next_sound _ _ hn) ?_
        intro mid' hm
        subst mid'
        exact ih mid h

end Machine.Arm64
