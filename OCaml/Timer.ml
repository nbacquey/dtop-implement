
let timer0 = ref 0.
let timer1 = ref 0.
let timer2 = ref 0.
let timer3 = ref 0.
let timer4 = ref 0.
let timer5 = ref 0.
let timer6 = ref 0.
let timer7 = ref 0.
let timer8 = ref 0.
let timer9 = ref 0.

let timerA = ref 0.
let timerB = ref 0.
let timerC = ref 0.

let start0 () = timer0 := !timer0 -. Unix.gettimeofday()
let start1 () = timer1 := !timer1 -. Unix.gettimeofday()
let start2 () = timer2 := !timer2 -. Unix.gettimeofday()
let start3 () = timer3 := !timer3 -. Unix.gettimeofday()
let start4 () = timer4 := !timer4 -. Unix.gettimeofday()
let start5 () = timer5 := !timer5 -. Unix.gettimeofday()
let start6 () = timer6 := !timer6 -. Unix.gettimeofday()
let start7 () = timer7 := !timer7 -. Unix.gettimeofday()
let start8 () = timer8 := !timer8 -. Unix.gettimeofday()
let start9 () = timer9 := !timer9 -. Unix.gettimeofday()

let startA () = timerA := !timerA -. Unix.gettimeofday()
let startB () = timerB := !timerB -. Unix.gettimeofday()
let startC () = timerC := !timerC -. Unix.gettimeofday()

let stop0 () = timer0 := !timer0 +. Unix.gettimeofday()
let stop1 () = timer1 := !timer1 +. Unix.gettimeofday()
let stop2 () = timer2 := !timer2 +. Unix.gettimeofday()
let stop3 () = timer3 := !timer3 +. Unix.gettimeofday()
let stop4 () = timer4 := !timer4 +. Unix.gettimeofday()
let stop5 () = timer5 := !timer5 +. Unix.gettimeofday()
let stop6 () = timer6 := !timer6 +. Unix.gettimeofday()
let stop7 () = timer7 := !timer7 +. Unix.gettimeofday()
let stop8 () = timer8 := !timer8 +. Unix.gettimeofday()
let stop9 () = timer9 := !timer9 +. Unix.gettimeofday()

let stopA () = timerA := !timerA +. Unix.gettimeofday()
let stopB () = timerB := !timerB +. Unix.gettimeofday()
let stopC () = timerC := !timerC +. Unix.gettimeofday()
