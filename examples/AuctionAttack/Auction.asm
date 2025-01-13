asm Auction

import ../../lib/asmeta/StandardLibrary
import ../../lib/asmeta/CTLlibrary
import ../../lib/solidity/EVMlibrary
import ../../lib/attackers/SimpleKingOfEtherThroneAttack

signature:

	dynamic controlled currentFrontrunner : StackLayer -> User
	dynamic controlled currentBid : StackLayer -> Integer
	
	dynamic controlled owner : StackLayer -> User


	/* USER and METHODS */
	static auction : User
	static user_owner : User
    static undef_user : User
	
	static bid : Function
	static destroy : Function
    static undef_function : Function

definitions:
	
	rule r_Save ($n in StackLayer) =
		par 
			currentFrontrunner($n) := currentFrontrunner(global_state_layer)
			currentBid($n) := currentBid(global_state_layer)
			owner($n) := owner(global_state_layer)
		endpar
		
		
	rule r_Destroy =
		if executing_function(current_layer) = destroy then
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Autodestroy[user_owner]
				case 1 : 
					r_Ret[]
			endswitch
		endif
	
	rule r_Bid = 
		if executing_function(current_layer) = bid then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Require[amount(current_layer) > currentBid(global_state_layer)]
				case 1 :
					if currentFrontrunner(global_state_layer) != undef_user then         // modified (it was 'isDef(...)'), because we cannot use 'undef'
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					else
						instruction_pointer(current_layer) := 4
					endif
				case 2 : 
					r_Transaction[auction, currentFrontrunner(global_state_layer), currentBid(global_state_layer), fallback]
				case 3 : 
					r_Require[call_response(current_layer+1)]
				case 4 : 
					par
						currentFrontrunner(global_state_layer) := sender(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 5 : 
					par
						currentBid(global_state_layer) := amount(current_layer) 
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 6 : 
					r_Ret[]
			endswitch
		endif
	
	rule r_Fallback_Auction = 
		if executing_function(current_layer) = fallback then 
			switch instruction_pointer(current_layer)
				case 0 : 
					r_Ret[]
			endswitch 
		endif
		
		
	CTLSPEC ag((sender(current_layer) = user and 
		executing_function(current_layer) = bid and 
		instruction_pointer(current_layer) = 0)
		implies af(currentFrontrunner(global_state_layer) = user)
	) 
	
	
	invariant over sender : executing_function(current_layer) = destroy implies 
					sender(current_layer) = owner(global_state_layer)
		
		
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
                            r_Transaction[user, random_user(stage), random_amount(stage), random_function(stage)]
                        endseq
                    else
                        switch executing_contract(current_layer)
                            case auction :
                                par 
                                    r_Bid[]
                                    r_Destroy[]
                                    r_Fallback_Auction[]
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
	function balance($c in User, $n in StackLayer) = if $n = 0 then  10 else -999999 endif
	function global_state_layer = 0
	function call_response($n in StackLayer) = false
	function disabled($u in User, $sl in StackLayer) = false
	function owner($sl in StackLayer) = user_owner

    // added initialisation of 'currentFrontrunner' to 'undef_user'
    //   because there in asm-symbolic-execution there is neither an undef 'undef'
    //   nor an implicit initial value of 'undef' for uninitialised functions
    function currentFrontrunner($n in StackLayer) = undef_user
	
	/*
	 * MODEL FUNCTION INITIALIZATION
	 */
    // use recognisable int value (-999999) instead of 'undef'
	function currentBid($n in StackLayer) = if $n = 0 then 0 else -999999 endif
