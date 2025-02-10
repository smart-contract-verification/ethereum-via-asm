asm Auction




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrary


signature:	
	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled currentFrontrunner : User
	dynamic controlled currentBid : MoneyAmount
	
	dynamic controlled owner : User


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
	 * MAIN 
	 */ 
	main rule r_Main = 
		if current_layer = 0 then
			if not exception then
				let ($s = random_sender) in
					let ($r = random_receiver) in
						let ($n = random_amount) in 
							let ($f = random_function) in
								if (not is_contract($s)) then
									r_Transaction[$s, $r, $n, $f]
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
	
		

	
	
