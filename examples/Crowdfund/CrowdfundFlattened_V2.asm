asm CrowdfundFlattened_V2




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
	dynamic controlled balance : User -> MoneyAmount 
	dynamic controlled destroyed : User -> Boolean
	static is_contract : User -> Boolean
	
	/* METHOD ATTRIBUTE */
	dynamic controlled payable : Function -> Boolean
	
	
	/* FUNCTIONS THAT ALLOW TRANSACTIONS */
	dynamic controlled sender : StackLayer -> User 
	dynamic controlled amount : StackLayer -> MoneyAmount
	
	/* STACK MANAGEMENT */
	dynamic controlled current_layer : StackLayer
	
	/* ALLOW FUNCTION EXECUTIONS */
	dynamic controlled executing_function : StackLayer -> Function
	dynamic controlled instruction_pointer : StackLayer -> InstructionPointer
	dynamic controlled executing_contract : StackLayer -> User
	
	/* RETURN VALUES */
	dynamic controlled boolean_return : Boolean
	
	/* GENERAL MONITORED FUNCTION */
	monitored random_sender : User
	monitored random_receiver : User
	monitored random_function : Function
	monitored random_amount : MoneyAmount
	
	/* EXCEPTION */
	dynamic controlled exception : Boolean
	
	
	
	/* ABSTRACT DOMAIN DEFINITION FOR EVM */
	static none : Function
	
	static user : User
	static user2 : User

	
	
	
	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled end_donate : GeneralInteger
	dynamic controlled goal : MoneyAmount
	dynamic controlled owner : User
	dynamic controlled donors : User -> MoneyAmount
	
	dynamic controlled local_amount : StackLayer -> MoneyAmount
	
	
	dynamic controlled block_number : GeneralInteger
	
	dynamic controlled old_balance : User -> MoneyAmount
	dynamic controlled old_donors : User -> MoneyAmount
	
	
	static crowdfund : User
	
	static donate : Function
	static withdraw : Function
	static reclaim : Function
	
	


	
	
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
		
		
	rule r_Transaction ($s in User, $r in User, $n in MoneyAmount, $f in Function) =
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
	 * DONATE FUNCTION RULE
	 */
	 
	rule r_Donate = 
		if executing_function(current_layer) = donate then
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[block_number <= end_donate]
				case 1 :
					par
						donors(sender(current_layer)) := amount(current_layer)
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 2 :
					r_Ret[]
			endswitch
		endif
		
	
	/* 
	 * WITHDRAW FUNCTION RULE
	 */
	rule r_Withdraw = 
		if executing_function(current_layer) = withdraw then
			switch instruction_pointer(current_layer)
				case 0 :
					r_Require[block_number >= end_donate]
				case 1 : 
					r_Require[balance(crowdfund) >= goal]
				case 2 : 
					let ($s = crowdfund, $r = sender(current_layer), $n = balance(crowdfund), $f = none) in
						r_Transaction[$s, $r, $n, $f]
					endlet
				case 3 : 
					r_Require[exception]
				case 4 :
					r_Ret[]
			endswitch
		endif
		
	/* 
	 * RECLAIM FUNCTION RULE
	 */	
	rule r_Reclaim = 
		if executing_function(current_layer) = reclaim then
			switch instruction_pointer(current_layer)
				case 0 :
					r_Require[block_number >= end_donate]
				case 1 : 
					r_Require[balance(crowdfund) < goal]
				case 2 : 
					r_Require[donors(sender(current_layer)) >= 0]
				case 3 : 
					par
						local_amount(current_layer) := donors(sender(current_layer))
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 4 :
					par
						donors(sender(current_layer)) := 0
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 5 : 
					let ($s = crowdfund, $r = sender(current_layer), $n = local_amount(current_layer), $f = none) in
						r_Transaction[$s, $r, $n, $f]
					endlet
				case 6 :
					r_Require[exception]
				case 7 : 
					r_Ret[]
			endswitch
		endif
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != reclaim and  executing_function(current_layer) != withdraw and  executing_function(current_layer) != donate then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */

	// se viene fatta una chiamata a donate, e non sono state sollevate eccezioni, allora donors(msg.sender) è maggiore di 0
	invariant over donors : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = donate and sender(1) = user and not exception) implies (donors(user) > 0)
	
	// anche se viene fatta una chiamata a donate e la fase di donazione è finita, non viene sollevata un eccezione
	invariant over exception : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = donate and block_number > end_donate) implies (not exception)

	// se viene completata una chiamata a withdraw senza che siano state alzate eccezioni, allora il sender era l'owner del contratto
	invariant over owner : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = withdraw and not exception) implies (sender(1) = owner)
	
	// se viene fatta una chiamata a reclaim ma tutti i donors valgono 0 allora viene alzata un'eccezione 
	invariant over exception : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = reclaim and not (exist $u in User with old_donors($u) > 0)) implies (exception)
	
	// se viene fatta una chiamta a reclaim da user, e il donors di user è maggiore di 0 allora dopo la chiamata donors vale 0
	invariant over donors : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = reclaim and sender(1) = user and old_donors(user) > 0) implies (donors(user) = 0) 
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		if current_layer = 0 then
			if not exception then
				let ($s = random_sender, $r = random_receiver, $n = random_amount, $f = random_function) in
					if not is_contract($s) then
						par
							block_number := block_number + 1
							r_Transaction[$s, $r, $n, $f]
							forall $u in User with true do
								par
									old_balance($u) := balance($u)
									old_donors($u) := donors($u)
								endpar
						endpar
					endif
				endlet
			endif
		else
			if executing_contract(current_layer) = crowdfund then
				par 
					r_Donate[]
					r_Withdraw[]
					r_Reclaim[]
					r_Fallback[]
				endpar
			endif
		endif
			






default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = none
	function executing_contract ($cl in StackLayer) = user
	function instruction_pointer ($sl in StackLayer) = 0
	function current_layer = 0
	function balance($c in User) = 3
	function destroyed($u in User) = false
	function payable($f in Function) = 
		switch $f
			case donate : true
			case none : true
			case withdraw : false
			case reclaim : false
			otherwise false
		endswitch
	function exception = false
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function owner = user
	function end_donate = 7
	function goal = 10
	
	function donors ($u in User) = 0
	
	function block_number = 0
		

	
	
