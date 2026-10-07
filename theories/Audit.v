From VerifiedRaft Require Import Safety Examples.

(* Compiled by scripts/check.py, which requires every audited theorem to be
   closed under the global context. The kernel checker then checks the .vo files. *)
Print Assumptions terms_do_not_decrease.
Print Assumptions vote_persistent.
Print Assumptions vote_consistency.
Print Assumptions log_matching.
Print Assumptions leader_append_only.
Print Assumptions committed_entries_remain.
Print Assumptions state_machine_safety.
Print Assumptions state_machine_safety_across_time.
Print Assumptions at_most_one_leader_per_term.
Print Assumptions election_safety.
Print Assumptions safety_preserved.
Print Assumptions reachable_invariant.
Print Assumptions trace_terms_monotone.
Print Assumptions trace_vote_persistent.
Print Assumptions trace_committed_entries_remain.
Print Assumptions trace_logs_append_only.
Print Assumptions committed_prefix_stable.
Print Assumptions applied_entries_are_committed.
Print Assumptions successful_trace.
Print Assumptions leadership_change_trace.
Print Assumptions duplicate_delivery_safe.
