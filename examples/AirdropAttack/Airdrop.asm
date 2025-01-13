asm Airdrop




import ../../lib/asmeta/CTLlibrary
import ../../lib/attackers/SimpleReentrancyAttack
import ../../lib/solidity/EVMlibrary
import ../../lib/asmeta/StandardLibrary


signature:	

	/* CONTRACT ATTRIBUTES, PARAMETERS AND RETURN VALUES */
	/* CONTRACT AIRDROP ATTRIBUTES */
	dynamic controlled user_balance : Prod(User, StackLayer) -> MoneyAmount // contract bank attribute 
	dynamic controlled received_airdrop : Prod(User, StackLayer) -> Boolean
	
	dynamic controlled airdrop_amount : StackLayer -> MoneyAmount
	
	/* METHODS DEFINITIONS AND USER DEFINITIONS */
	static airdrop : User
    static undef_user : User
	
	static receive_airdrop : Function
	static can_receive_airdrop : Function
    static undef_function : Function

	
	
definitions:



	rule r_Save ($n in StackLayer) = 
		par
			forall $u in User with true do
				par
					user_balance($u, $n) := user_balance($u, global_state_layer)
					received_airdrop($u, $n) := received_airdrop($u, global_state_layer)
				endpar
			airdrop_amount($n) := airdrop_amount(global_state_layer)
		endpar
	
	
	
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
							r_Require[not received_airdrop(sender($cl), global_state_layer)]
						case 1 : 
							r_Transaction[airdrop, sender($cl), 0, can_receive_airdrop]
						case 2 :
							r_Require[boolean_return(global_state_layer)]
						case 3 : 
							par
								user_balance(sender($cl), global_state_layer) := user_balance(sender($cl), global_state_layer) + airdrop_amount(global_state_layer)
								received_airdrop(sender($cl), global_state_layer) := true
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
	 
	 invariant over user_balance : (forall $u in User with user_balance($u, global_state_layer) <= airdrop_amount(global_state_layer))

		
	
	/*
	 * MAIN 
	 */ 
	main rule r_Main =
        if random_user (stage) != undef_user
        then
            par
                if transaction then 
                    seq
                        r_Save[global_state_layer + 1]
                        r_Save_Env[global_state_layer + 1]
                        r_Save_Att[global_state_layer + 1]
                        global_state_layer := global_state_layer + 1
                        r_Transaction_Env[]
                    endseq
                else
                    if current_layer = 0 then
                        seq
                            par 
                                r_Save[0]
                                r_Save_Env[0]
                                global_state_layer := 0
                            endpar
                            r_Transaction[user, random_user (stage), 1, random_function (stage)]
                        endseq
                    else
                        switch executing_contract(current_layer) 
                            case airdrop :
                                par 
                                    r_Receive_airdrop[]
                                    r_Fallback_Airdrop[]
                                endpar
                            case attacker :
                                r_Attacker[]
                            otherwise 
                                r_Ret[]
                        endswitch
                    endif
                endif
                stage := stage + 1
            endpar
        endif
		





default init s0:
    function stage = 0

	/*
	 * LIBRARY FUNCTION INITIZLIZATIONS
	 */
	function executing_function ($sl in StackLayer) = if $sl = 0 then none else undef_function endif 
	function executing_contract ($cl in StackLayer) = if $cl = 0 then user else undef_user endif

    // use recognisable int value (-999999) instead of 'undef'
	function instruction_pointer ($sl in StackLayer) = if $sl = 0 then 0 else -999999 endif

	function current_layer = 0
	function transaction = false

    // use recognisable int value (-999999) instead of 'undef'
	function balance($c in User, $n in StackLayer) = if $n = 0 then 10 else -999999 endif
	function global_state_layer = 0
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
    // use recognisable int value (-999999) instead of 'undef'
	function user_balance($c in User, $n in StackLayer) = if $n = 0 then  0 else -999999 endif
	
    // !!! in place of 'undef', would true be any better than false in 'else' branch ?
    function received_airdrop($u in User, $n in StackLayer) = if $n = 0 then false else false endif    // if $n = 0 then false endif

    // use recognisable int value (-999999) instead of 'undef'
	function airdrop_amount ($n in StackLayer) = if $n = 0 then 3 else -999999 endif
		

	
	
