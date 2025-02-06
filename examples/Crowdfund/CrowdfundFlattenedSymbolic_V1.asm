asm CrowdfundFlattenedSymbolic_V1




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrarySymbolic


signature:	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled end_donate : Integer
	dynamic controlled goal : Integer
	dynamic controlled owner : User
	dynamic controlled donors : User -> Integer
	
	dynamic controlled local_amount : Integer -> Integer
	
	
	dynamic controlled block_number : Integer
	
	dynamic controlled old_balance : User -> Integer
	dynamic controlled old_donors : User -> Integer
	
	
	static crowdfund : User
	static user2 : User
	
	static donate : Function
	static withdraw : Function
	static reclaim : Function
	
	


	
	
definitions:
	
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
					let ($cl = current_layer) in
						r_Transaction[crowdfund, sender($cl), balance(crowdfund), none]
					endlet
				case 3 : 
					r_Require[not exception]
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
						donors(sender(current_layer)) := 1
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1 
					endpar
				case 5 : 
					let ($cl = current_layer) in
						r_Transaction[crowdfund, sender($cl), local_amount($cl), none]
					endlet
				case 6 :
					r_Require[not exception]
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
	 * INVARIANT - S_24
	 */
	// se viene fatta una chiamata a donate, e non sono state sollevate eccezioni, allora donors(msg.sender) è maggiore di 0 - ~ S_4
	invariant over donors : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = donate and sender(1) = user and not exception) implies (donors(user) > 0)
	
	// anche se viene fatta una chiamata a donate e la fase di donazione è finita, non viene sollevata un eccezione - S_4
	invariant over exception : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = donate and block_number > end_donate) implies (not exception)

	// se viene completata una chiamata a withdraw senza che siano state alzate eccezioni, allora il sender era l'owner del contratto - S_7
	invariant over owner : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = withdraw and not exception) implies (sender(1) = owner)
	
	// dopo una chiamata a reclaim, se non vengono sollevate eccezioni, allora il valore di donors per il sender è 0 - S_10
	invariant over exception : (current_layer = 0 and executing_contract(1) = crowdfund and executing_function(1) = reclaim and not exception) implies (donors(sender(1)) = 0)
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 
		par
			if current_layer = 0 then
				if not exception then
					let ($s = user) in
						let ($r = random_receiver(stage)) in
							let ($n = random_amount(stage)) in 
								let ($f = random_function(stage)) in
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
									else 
										exception := false
									endif
								endlet
							endlet
						endlet
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
			case donate : true
			case none : true
			case withdraw : false
			case reclaim : false
			otherwise false
		endswitch
	function exception = false
	
	function stage = 0

	function is_contract ($u in User) =
		switch $u 
			case user : false
			case user2 : false
			otherwise true
		endswitch
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function owner = user2
	function end_donate = 2
	function goal = 10
	
	function donors ($u in User) = 0
	
	function block_number = 0
		

	
	
