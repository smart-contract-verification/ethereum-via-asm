asm BazSymbolic_V1




import ../../lib/asmeta/StandardLibrary


signature:	

	





	/* --------------------------------------------LIBRARY MODEL DOMAINS-------------------------------------------- */
	
	
	
	
	abstract domain Function
	abstract domain User
	domain MoneyAmount subsetof Integer
	domain StackLayer subsetof Integer
	domain InstructionPointer subsetof Integer
	domain GeneralInteger subsetof Integer
	
	
	
	/* --------------------------------------------CONTRACT MODEL DOMANIS-------------------------------------------- */
	
	enum domain State = {INTRANSITION, INITIALSTATE}
	
	
	/* --------------------------------------------LIBRARY MODEL FUNCTIONS-------------------------------------------- */
	
	/* USER ATTRIBUTES */
	dynamic controlled balance : User -> Integer 
	dynamic controlled destroyed : User -> Boolean
	static is_contract : User -> Boolean
	
	/* METHOD ATTRIBUTE */
	dynamic controlled payable : Function -> Boolean
	
	/* FUNCTIONS THAT ALLOW TRANSACTIONS */
	dynamic controlled sender : Integer -> User 
	dynamic controlled amount : Integer -> Integer
	
	/* STACK MANAGEMENT */
	dynamic controlled current_layer : Integer
	
	/* ALLOW FUNCTION EXECUTIONS */
	dynamic controlled executing_function : Integer -> Function
	dynamic controlled instruction_pointer : Integer -> Integer
	dynamic controlled executing_contract : Integer -> User
	
	/* RETURN VALUES */
	dynamic controlled boolean_return : Boolean
	
	/* GENERAL MONITORED FUNCTION */
	controlled random_sender : Integer -> User
	controlled random_receiver : Integer -> User
	controlled random_function : Integer -> Function
	controlled random_amount : Integer -> Integer
	
	/* EXCEPTION */
	dynamic controlled exception : Boolean
	
	controlled stage : Integer
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User

	
	
	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled state1 : Boolean
	dynamic controlled state2 : Boolean
	dynamic controlled state3 : Boolean
	dynamic controlled state4 : Boolean
	dynamic controlled state5 : Boolean
	
	controlled a_mon : Integer -> Integer
	controlled b_mon : Integer -> Integer
	controlled c_mon : Integer -> Integer
	
	controlled a : Integer
	controlled b : Integer
	controlled c : Integer
	
	controlled d : Integer


	/* USER and METHODS */
	static u_baz : User
	
	static f_baz : Function
	
	


	
	
definitions:

	/* --------------------------------------------LIBRARY MODEL-------------------------------------------- */


	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-1 : 7}
	domain StackLayer = {0 : 2}
	domain InstructionPointer = {0 : 7}
	domain GeneralInteger = {-10 : 10}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			otherwise true
		endswitch
		

	/* 
	 * RETURN RULE
	 */
	macro rule r_Ret =
		current_layer := current_layer - 1 
		
		
	rule r_Transaction ($s in User, $r in User, $n in Integer, $f in Function) =
		if $n >= 0 and balance($s) >= $n and $s != $r and ((is_contract($r) implies (not destroyed($r)))) and ((is_contract($r) and $n > 0) implies (payable($f))) then 
			par
				seq
					balance($s) := balance($s) - $n 
					balance($r) := balance($r) + $n
				endseq
				if is_contract($r) then
					par
						sender(current_layer + 1) := $s // set the transition attribute to the sender user
						amount(current_layer + 1) := $n // set the transaction attribute to the amount of coin to transfer
						current_layer := current_layer + 1
						executing_contract(current_layer + 1) := $r
						executing_function(current_layer + 1) := $f
						instruction_pointer(current_layer + 1) := 0
						exception := false
					endpar
				endif
				if is_contract($s) then 
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endif
			endpar
		else 
			par
				if is_contract($s) then 
					r_Ret[]
				endif
				exception := true
			endpar
		endif
		

		
	/*
	 * REQUIRE RULE
	 */
	macro rule r_Require ($b in Boolean) = 
		let ($cl = current_layer) in
			if $b then
				instruction_pointer($cl) := instruction_pointer($cl) + 1
			else 
				par
					r_Ret[]
					exception := true
				endpar
			endif
		endlet
		
		
	macro rule r_Selfdestruct ($u in User) =
		if is_contract(executing_contract(current_layer)) then
			par
				balance(executing_contract(current_layer)) := 0
				balance($u) := balance($u) + balance(executing_contract(current_layer))
				destroyed(executing_contract(current_layer)) := true
				r_Ret[]
			endpar
		endif
		
	
	
	/* --------------------------------------------CONTRACT MODEL-------------------------------------------- */

	/* 
	 * DESTROY FUNCTION RULE
	 */
		
	
	/* 
	 * BAZ FUNCTION RULE
	 */
	rule r_Baz = 
		if executing_function(current_layer) = f_baz then 
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						a := a_mon(stage)
						b := b_mon(stage)
						c := c_mon(stage)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 :
					par
						d := b + c
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 2 : 
					if d < 1 then 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					else
						instruction_pointer(current_layer) := 6
					endif
				case 3 : 
					if b < 3 then
						par
							state1 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 4 : 
					if a = 42 then
						par
							state2 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 5 : 
					par
						state3 := true
						r_Ret[]
					endpar
				case 6 : 
					if c < 42 then
						par
							state4 := true
							r_Ret[]
						endpar
					else 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endif
				case 7 : 
					par
						state5 := true
						r_Ret[]
					endpar
			endswitch
		endif
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != f_baz then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	 
	 invariant over state1, state2, state3, state4, state5 : ((not state1) or (not state2) or (not state3) or (not state4) or (not state5))
	 //invariant over state1, state2, state3, state4, state5 : not state4

	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par
			if current_layer = 0 then
				if not exception then
					let ($r = random_receiver(stage)) in
						let ($n = random_amount(stage)) in 
							let ($f = random_function(stage)) in
								r_Transaction[user, $r, $n, $f]
							endlet
						endlet
					endlet
				endif
			else
				if executing_contract(current_layer) = u_baz then
					par 
						r_Baz[]
						r_Fallback[]
					endpar
				endif
			endif
			stage := stage + 1
		endpar
			






default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in Integer) = none
	function executing_contract ($cl in Integer) = user
	function instruction_pointer ($sl in Integer) = 0
	function current_layer = 0
	function balance($c in User) = 3
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case f_baz : false
			otherwise false
		endswitch
	function exception = false
	
	function stage = 0
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function state1 = false
	function state2 = false
	function state3 = false
	function state4 = false
	function state5 = false
	
		

	
	
