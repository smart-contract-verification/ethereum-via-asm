asm AuctionFlattened_V1




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

	dynamic controlled currentFrontrunner : User
	dynamic controlled currentBid : MoneyAmount
	
	dynamic controlled owner : User
	
	controlled old_frontrunner : User
	controlled old_bid : MoneyAmount
	controlled old_balance : User -> MoneyAmount


	/* USER and METHODS */
	static auction : User
	
	static bid : Function
	static destroy : Function
	
	


	
	
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
	 * DESTROY FUNCTION RULE
	 */
	 
	rule r_Destroy =
		if executing_function(current_layer) = destroy then
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Selfdestruct[owner]
			endswitch
		endif
		
	
	/* 
	 * BID FUNCTION RULE
	 */
	rule r_Bid = 
		if executing_function(current_layer) = bid then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[amount(current_layer) > currentBid]
				case 1 :
					if isDef(currentFrontrunner) then 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					else
						instruction_pointer(current_layer) := 4
					endif
				case 2 : 
					r_Transaction[auction, currentFrontrunner, currentBid, none]
				case 3 : 
					r_Require[exception]
				case 4 : 
					par
						currentFrontrunner := sender(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 : 
					par
						currentBid := amount(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 6 : 
					r_Ret[]
			endswitch
		endif
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	
	
	rule r_Fallback =
		if executing_function(current_layer) != bid and  executing_function(current_layer) != destroy then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[false]
			endswitch
		endif
	
	

		
		
	/* --------------------------------------------MAIN AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */

	// la funzione destroy può venir chiamata solamente dall'owner del contratto
	invariant over sender : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = destroy and not exception) implies (sender(1) = owner)
	
	// se viene fatta una chiamata alla funzione bid ed esiste già un current_frontrunner, a questo vengono ritornati i soldi precedentemente versati
	invariant over balance : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = bid and isDef(old_frontrunner) and not exception and old_frontrunner = user and sender(1) = user) implies (old_balance(user) + old_bid = balance(user))
	
	// se faccio una chiamata alla funzione bid con un msg.value maggiore di current_bid allora divento il nuovo current_frontrunner
	invariant over balance : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = bid and amount(1) > old_bid and not exception) implies (currentFrontrunner = sender(1))
	
	// se viene fatta una chiamata alla funzione destroy, tutti i soldi del contratto vanno all'owner
	invariant over balance : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = destroy and not exception) implies (old_balance(user) + old_balance(auction) = balance(user))


	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		if current_layer = 0 then
			if not exception then
				let ($s = random_sender, $r = random_receiver, $n = random_amount, $f = random_function) in
					if not is_contract($s) then
						par
							r_Transaction[$s, $r, $n, $f]
							old_bid := currentBid
							old_frontrunner := currentFrontrunner
							forall $u in User with true do
								old_balance($u) := balance($u)
						endpar
					else 
						exception := true
					endif
				endlet
			endif
		else
			if executing_contract(current_layer) = auction then
				par 
					r_Destroy[]
					r_Bid[]
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
			case destroy : false
			case bid : true
			otherwise false
		endswitch
	function exception = false
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function owner = user2
	function currentBid = 0
	
	function old_balance ($u in User) = 0
	function old_bid = 0
	function old_frontrunner = user
		

	
	
