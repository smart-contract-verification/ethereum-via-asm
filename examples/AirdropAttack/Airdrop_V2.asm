asm Airdrop_V2




import ../../lib/asmeta/StandardLibrary
import ../../lib/solidity/EVMLibrarySymbolic

signature:	
	
	/* --------------------------------------------CONTRACT MODEL FUNCTIONS-------------------------------------------- */

	dynamic controlled user_balance : User -> Integer 
	dynamic controlled received_airdrop : User -> Boolean
	dynamic controlled old_received_airdrop : User -> Boolean
	
	dynamic controlled airdrop_amount : Integer
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static airdrop : User
	
	static user2 : User
	
	static receive_airdrop : Function
	static can_receive_airdrop : Function
	
	


	
	
definitions:
	
	
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
	 * INVARIANT - S_11
	 */
	
	// se viene fatta una chiamata a receive_airdrop e non sono state alzate eccezioni, il valore per msg.sender di received_airdrop rimane true - S_5
	invariant over received_airdrop : (current_layer = 0 and executing_contract(1) = airdrop and executing_function(1) = receive_airdrop and not exception and sender(1) = user)implies(not received_airdrop(user))
	
	// if a call to receive_airdrop is made from an account with received_airdrop set to 0, an exception is not raised - S_3
	invariant over exception : (current_layer = 0 and executing_contract(1) = airdrop and executing_function(1) = receive_airdrop and sender(1) = user and not old_received_airdrop(user)) implies (not exception)
	
	// not all users received the airdrop - S_4
	invariant over user_balance : not (forall $u in User with (not is_contract($u)) implies received_airdrop($u))
		
		
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
	
	function is_contract ($u in User) =
		switch $u 
			case user : false
			case user2 : false
			otherwise true
		endswitch
	
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function user_balance($c in User) = 0
	function received_airdrop($u in User) = false
	function airdrop_amount = 1
		

	
	
