len(s) should give be implemented as an operator to take the length of the
string.

  $ nuscr PasswordManager.nuscr --project C@PasswordManager --show-solver-queries
  (declare-const freshvar$0 String)
  (declare-const stored_pass String)
  (assert (not (>= (str.len stored_pass) 6)))
  (assert (= freshvar$0 "password"))
  (assert (= freshvar$0 stored_pass))
  (check-sat)
  
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]

PasswordManager2 has a too short initial password, and an error is expected.

  $ nuscr PasswordManager2.nuscr --project C@PasswordManager --show-solver-queries
  (declare-const freshvar$0 String)
  (declare-const stored_pass String)
  (assert (not (>= (str.len stored_pass) 6)))
  (assert (= freshvar$0 "pass"))
  (assert (= freshvar$0 stored_pass))
  (check-sat)
  
  nuscr: Reported problem:
          ("Unix.Unix_error(Unix.ENOENT, \"create_process\", \"z3\")")
  [124]
