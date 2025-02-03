asm KotetFlattenedSymbolic_V2




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
	static user2 : User

	
	
	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled king : User
	dynamic controlled claim_price : Integer
	
	dynamic controlled owner : User
	
	dynamic controlled old_king : User
	dynamic controlled old_claim_price  : Integer
	
	static kotET : User
	
	


	
	
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
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		switch instruction_pointer(current_layer) 
			case 0: 
				r_Require[amount(current_layer) >= claim_price]
			case 1 :
				r_Require[(not (sender(current_layer) = owner)) implies (sender(current_layer) != king)]
			case 2: 
				r_Transaction[kotET, king, claim_price + 2, none]
			case 3: 
				par
					king := sender(current_layer)
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 4:
				par
					claim_price := claim_price + 1
					instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
				endpar
			case 5 : 
				r_Ret[]
		endswitch
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	 
	 // ogni volta che un utente diventa king deve essere un utente diverso dal king precedente
	 invariant over king : (current_layer = 0 and not exception and executing_contract(1) = kotET) implies (old_king != king)
	 
	 // non è possibile che il balance del contratto arrivi a 0
	 invariant over balance : (not exception) implies balance(kotET) > 0
	 	 
	 // claim price non può essere maggiore di tutti i balance degli utenti
	 invariant over claim_price : not (forall $u in User with balance($u) < claim_price )
	 
	 // se viene fatta una chiamata alla fallback di Kotet con un amount maggiore o uguale a claim_price non viene sollevata un eccezioe 
	 invariant over king : (current_layer = 0 and executing_contract(1) = kotET and amount(1) >= old_claim_price) implies (not exception)




	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par
			if current_layer = 0 then
				if not exception then
					let ($s = random_sender(stage)) in
						let ($r = random_receiver(stage)) in
							let ($n = random_amount(stage)) in 
								let ($f = random_function(stage)) in
									if not is_contract($s) then
										par
											r_Transaction[$s, $r, $n, $f]
											old_king := king
											old_claim_price := claim_price
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
				if executing_contract(current_layer) = kotET then
					r_Fallback[]
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
	function payable($f in Function) = true
	function exception = false
	
	function stage = 0
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	 
	function owner = user2
	
	function king = user 
	function claim_price = 1
		

	
	
