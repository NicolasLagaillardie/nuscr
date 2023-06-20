The protocol with recursion variable should be well-formed.
  $ nuscr Recursion.nuscr --project A@Recursion1 --show-solver-queries
  (declare-const count Int)
  (declare-const freshvar$2 Int)
  (assert (not (>= count 0)))
  (assert (= freshvar$2 0))
  (assert (= freshvar$2 count))
  (check-sat)
  
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]



  $ nuscr Recursion.nuscr --project A@Recursion2 --show-solver-queries
  (declare-const count Int)
  (declare-const freshvar$2 Int)
  (assert (not (>= count 0)))
  (assert (= freshvar$2 0))
  (assert (= freshvar$2 count))
  (check-sat)
  
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]

When projected on B, the recursion variable `count` should not appear.

  $ nuscr Recursion.nuscr --project B@Recursion1
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]

  $ nuscr Recursion.nuscr --project B@Recursion2
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]
