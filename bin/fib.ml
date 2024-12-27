let n = 43
let rec fib n = if n < 2 then 1 else fib n - 1 + fib n - 2

let () =
  let d = Domain.spawn (fun _ -> fib n) in
  print_int (Domain.join d)
