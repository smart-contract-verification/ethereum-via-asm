asm Airdrop




import ../../Libraries/CTLlibrary
import ../../SolidityLibraries/SimpleReentrancyAttack
import ../../SolidityLibraries/EVMlibrary
import ../../Libraries/StandardLibrary


signature:	

	/* CONTRACT ATTRIBUTES, PARAMETERS AND RETURN VALUES */
	/* CONTRACT AIRDROP ATTRIBUTES */
	dynamic controlled user_balance : User -> MoneyAmount // contract bank attribute 
	dynamic controlled received_airdrop : User -> Boolean
	
	dynamic controlled airdrop_amount : MoneyAmount
	
	/* CAN RECEIVE AIRDROP FUNCTIONS */
	dynamic controlled can_receive_airdrop_return : Boolean
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static airdrop : User
	
	static receive_airdrop : Function
	static can_receive_airdrop : Function


	
	
definitions:
	
	
	
	/* --------------------------------------------AIRDROP CONTRACT IMPLEMENTATION-------------------------------------------- */

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
							r_Transaction[airdrop, sender($cl), 0, can_receive_airdrop]
						case 2 :
							r_Require[boolean_return]
						case 3 : 
							par
								user_balance(sender($cl)) := user_balance(sender($cl)) + airdrop_amount
								received_airdrop(sender($cl)) := true
								instruction_pointer($cl) := instruction_pointer($cl) + 1
							endpar
						case 4 : 
							r_Ret[]
					endswitch
				endif
			endlet
		endlet
	
	
	
	/* 
	 * FALLBACK FUNCTION RULE
	 */ 
	 
	rule r_Fallback_Airdrop =
		let ($cl = current_layer) in
			if executing_function($cl) != receive_airdrop then 
				switch instruction_pointer($cl)
					case 0 : 
						 r_Ret[]
				endswitch
			endif
		endlet	
		
		
	/* --------------------------------------------MAINS AND INVARIANTS-------------------------------------------- */
		

	/*
	 * INVARIANT
	 */
	 
	 invariant over user_balance : (forall $u in User with user_balance($u) <= airdrop_amount)

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main = 	
		if not is_contract(executing_contract(current_layer)) then
			r_Transaction[user, random_user, 1, random_function]
		else
			if executing_contract(current_layer) = airdrop then
				par 
					r_Receive_airdrop[]
					r_Fallback_Airdrop[]
				endpar
			else 
				r_Attacker[]
			endif
		endif
			
		





default init s0:
	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = if $sl = 0 then none endif 
	function executing_contract ($cl in StackLayer) = if $cl = 0 then user endif
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 endif
	function current_layer = 0
	function balance($c in User) = 10
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
	function user_balance($c in User) = 0
	function received_airdrop($u in User) = false
	function airdrop_amount = 3
		

	
	
