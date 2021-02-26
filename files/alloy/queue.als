// @file: queue alloy
// @version: draft
module queues
open util/ordering[Generation]
open util/ternary

sig Generation {}

sig Message {}

one sig System {
  , var generation: one Generation
  , var queue : Message -> Generation
  , var received :  Message -> Generation
}

pred init {
  no queue
  no received
  System.generation = Generation <: first
}

pred skip[] {
  queue' = queue
  received' = received
  generation' = generation
}

pred publish[m: Message] {
  queue' = queue ++ System -> m -> System.generation

  received' = received
  generation' = generation
}

pred consume[m: Message] {
	let gen = System.queue[m] | {
    some gen

    received' = received ++ System -> m -> gen
    queue' = queue - System -> m -> gen
  }
  generation' = generation
}

pred receive[m: Message] {
	let gen = System.queue[m] | {
    some gen

    received' = received ++ System -> m-> gen
  }

	queue' = queue
  generation' = generation
}

pred nextGeneration[] {
  some generation.next

  queue' = queue
  received' = received
  generation' = generation.next
}

fact traces {
  init
  always (
    skip[] or 
	nextGeneration[] or 
    (some m: Message | publish[m] or consume[m] or receive[m])
  )
}

liveness: check {
  eventually (
		let lastGeneration = (Generation <: last) {
      all g: ran[received] | g = lastGeneration
    }
  )	
} for 5 but 2 Generation

run {
	some Message
  eventually (
		let lastGeneration = (Generation <: last) {
			System.generation = lastGeneration
      all m: Message | System.received[m] = lastGeneration
    }
  )
} for 5 but 2 Generation
