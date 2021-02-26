-- alloy4.2-rc.jar on http://alloy.mit.edu/community/node/1039
open util/ordering [system state].

sig philosopher {
	disj left fork, right fork: one fork,
	left, right: one philosopher
}
sig fork { disj 
	disj left, right: one philosopher
}
fact Philosophers and forks are alternating in a row {
	#philosopher = #fork
	-- there is a fork on both sides of the philosopher.
	(all p: philosopher | p. left = p. left fork. left and p.right = p.right fork. Right )
	-- There is a philosopher on both sides of the fork.
	(all f: fork | f = f. left. Right fork and f = f.Right. Left fork )
}

fact The table is one {.
	-- the left (right) transitive closure contains the entire philosopher
	(all p: philosophers | philosophers in p.^right and philosophers in p.^left)
	-- left. Left fork (Right. Left fork (Right fork) transitive closure contains the whole fork
	(all f: fork | fork in f.^( left. Left fork ) and fork in f.^( Right. Right fork ))
}

-- Global system state
sig system state {
     -- fork has at most one holder (none:left or equal to one)
	Holder: fork -> lone philosopher
}{
	-- a fork can only be held by the philosophers on either side of itself
	all f:fork | holder[f] in f.(left+right)
}
-- predicate for fork
pred available ( s: system state, f: fork ) {
	no s.holder [ f ]
}

-- predicate for philosopher
pred eating ( s: system state, p: philosopher ) { no
	p = s.holder [p.right fork] and p = s.holder [p.left fork] }
}

-- Algorithm.
-- s' is the next state in which philosopher p has made an action in state s.
pred Take the left fork ( s: system state, s': system state, p: philosopher ) {
	-- In s, the left fork of p is available, and in s', the left fork of p is held by p.
	-- (use [] to apply an argument to a predicate)
	Available[s,p. left fork] and s'. Held by [p. left fork] = p
	-- all other forks have unchanged holders
	and (all f: (fork - p.left fork) | s.holder[f] = s'. Retainer[f])
}
pred Take the right fork ( s: system state, s': system state, p: philosopher ) {
	Available[s,p. left fork] and s'. Retainer[p. right fork] = p
	and (all f: (fork - p.right fork) | s.holder[f] = s'. Retainer[f])
}
pred Let go of both forks (s:system state, s':system state, p:philosopher){
	eat[s,p] and (available[s',p. right fork] and available[s',p. left fork])	
	and (all f: (fork - (p.left fork + p.right fork)) | s.holder[f] = s'. Retainer[f])
}

-- Initial state predicate
pred no one has it ( s: system state ) {
	all f: fork | available [ s, f ])
}
-- constraint on all orderings on a state
fact Constraint on state transitions { all
	-- first satisfies no one has
	No one has [ first ]. 
	-- state s other than the last state is.
	-- if someone can operate, then the next state next[s] after s is the state after someone moves, and
	-- If not, nothing has changed (deadlock is still in effect).
	all s: system state - last
		| someone can move [s] => someone moves [s,next[s]] else s.holder = next[s]. Retainer
} 
-- In state s, s' is the state in which someone has moved.
pred someone moves ( s: system state, s': system state ) {
	some p: philosopher | take left fork [ s, s', p ] or take right fork [ s, s', p ] or let go of both forks [s,s',p]. 
}
-- Someone can operate in state s.
pred Someone can operate in (s: system state){
	some p: philosopher | 
		available[s,p. left fork] or available[s,p. right fork] or eating[s,p].
}

pred Execution with deadlock present {
	some s:system state | not someone can run [s]. 
				and all s': s.^next | not someone can run [s'] -- all s' after s are deadlocked
				and all s'': s.^prev | someone can run [s''] -- someone can run all s' before s
}
-- command to find the execution where the deadlock exists.
-- 3 forks, 3 philosophers, run length is 20 steps
run execution for which deadlock exists exactly 3 forks, 3 philosophers, 10 system states

Translated with www.DeepL.com/Translator (free version)
