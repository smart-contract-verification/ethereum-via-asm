asm AuctionFlattenedSymbolic_V1




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrarySymbolic


signature:	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled currentFrontrunner : User
	dynamic controlled currentBid : Integer
	
	dynamic controlled owner : User
	
	controlled old_frontrunner : User
	controlled old_bid : Integer
	controlled old_balance : User -> Integer


	/* USER and METHODS */
	static auction : User
	static undef_user : User
	
	static user2 : User
	
	static bid : Function
	static destroy : Function
	
	


	
	
definitions:
	
	
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
					if currentFrontrunner != undef_user then 
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

	// The destroy function can only be called by the owner of the contract - S_2
	invariant over sender : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = destroy and not exception and destroyed(auction)) implies (sender(1) = owner)
	
	// If a call is made to the bid function and a current_frontrunner already exists, the previously deposited money is returned to it
	invariant over balance : (current_layer = 1 and instruction_pointer(1) = 6 and executing_contract(1) = auction and executing_function(1) = bid and old_frontrunner != undef_user and not exception and old_frontrunner = user and sender(1) = user) implies (old_balance(user) + old_bid = balance(user))
	
	// if I make a call to the bid function with a msg.value greater than current_bid then I become the new current_frontrunner
	invariant over balance : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = bid and amount(1) > old_bid and not exception) implies (currentFrontrunner = sender(1))
	
	// if a call is made to the destroy function, all the money in the contract goes to the owner - S_2
	invariant over balance : (current_layer = 0 and executing_contract(1) = auction and executing_function(1) = destroy and not exception) implies (old_balance(user) + old_balance(auction) = balance(user))


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
									if (not is_contract($s)) then
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
							endlet
						endlet
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
			case destroy : false
			case bid : true
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
	function currentFrontrunner = undef_user
	function owner = user2
	function currentBid = 0
	
		

	
	
