asm AirdropFlattenedSymbolic_V2




import ../../lib/asmeta/StandardLibrary


signature:	

	





	/* --------------------------------------------LIBRARY MODEL DOMAINS-------------------------------------------- */
	
	
	
	
	abstract domain Function
	abstract domain User
	domain MoneyAmount subsetof Integer
	domain StackLayer subsetof Integer
	domain InstructionPointer subsetof Integer
	
	
	
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
	controlled random_user : Integer -> User
	controlled random_function : Integer -> Function
	controlled random_amount : Integer -> Integer
	
	/* EXCEPTION */
	dynamic controlled exception : Boolean
	
	dynamic controlled stage : Integer
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User
	static user2 : User
	
	
	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled user_balance : User -> Integer 
	dynamic controlled received_airdrop : User -> Boolean
	dynamic controlled old_received_airdrop : User -> Boolean
	
	dynamic controlled airdrop_amount : Integer
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static airdrop : User
	
	static receive_airdrop : Function
	static can_receive_airdrop : Function
	
	


	
	
definitions:

	/* --------------------------------------------LIBRARY MODEL-------------------------------------------- */


	/* DOMAIN AND FUNCTION DEFINITION */
	domain MoneyAmount = {-1 : 7}
	domain StackLayer = {0 : 2}
	domain InstructionPointer = {0 : 7}
	
	
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			case user2 : false
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
	 * DEPOSIT FUNCTION RULE
	 */
	 
	rule r_Receive_airdrop =
		let ($cl = current_layer) in
			let ($scl = sender($cl)) in
				if executing_function($cl) = receive_airdrop then 
					switch instruction_pointer($cl)
						case 0 : 
							r_Require[not received_airdrop(sender($cl))]
						case 1 : 
							r_Transaction[airdrop, sender($cl), 1, can_receive_airdrop]
						case 2 : 
							par
								user_balance(sender($cl)) := user_balance(sender($cl)) + airdrop_amount
								received_airdrop(sender($cl)) := true
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endpar
						case 3 : 
							r_Ret[]
					endswitch
				endif
			endlet
		endlet
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != receive_airdrop then 
			switch instruction_pointer(current_layer)
				case 0 : 
					 r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	
	// anche se viene fatta una chiamata a receive_airdrop e non sono state alzate eccezioni, il valore per msg.sender di received_airdrop rimane false
	invariant over received_airdrop : (current_layer = 0 and executing_contract(1) = airdrop and executing_function(1) = receive_airdrop and not exception and sender(1) = user)implies(not received_airdrop(user))
	
	// se viene fatta una chiamata a receive_airdrop da un account con received_airdrop a 0, non viene sollevata un eccezione
	invariant over exception : (current_layer = 0 and executing_contract(1) = airdrop and executing_function(1) = receive_airdrop and sender(1) = user and not old_received_airdrop(user)) implies (not exception)
	
	// non tutti gli utenti hanno ricevuto l'airdrop
	invariant over user_balance : not (forall $u in User with (not is_contract($u)) implies received_airdrop($u))
		
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par
			if current_layer = 0 then
				if not exception then
					let ($s = random_sender(stage)) in
						let ($r = random_user(stage)) in 
							let ($n = random_amount(stage)) in 
								let($f = random_function(stage)) in
									if not is_contract($s) then
										par
											r_Transaction[$s, $r, $n, $f]
											forall $u in User with true do
												old_received_airdrop($u) := received_airdrop($u)
										endpar
									else
										exception := true
									endif
								endlet
							endlet
						endlet
					endlet
				endif
			else
				if executing_contract(current_layer) = airdrop then
					par 
						r_Receive_airdrop[]
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
	//function balance($c in User) = 3
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case receive_airdrop : false
			case none : true
			otherwise false
		endswitch
	function exception = false
	
	function stage = 0
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function user_balance($c in User) = 0
	function received_airdrop($u in User) = false
	function airdrop_amount = 1
		

	
	
