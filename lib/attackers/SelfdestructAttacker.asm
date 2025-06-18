module SelfdestructAttacker


import ../solidity/EVMLibrary
import ../asmeta/StandardLibrary


export *


signature:

	controlled input_user : StackLayer -> User
	
	static attacker : User
	
	static attack : Function


definitions:

    rule r_Save_Att ($n in StackLayer) = 
		skip

	rule r_Attack =
		if executing_function(current_layer) = attack then
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						input_user(current_layer) := random_user
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Selfdestruct[input_user(current_layer)]
			endswitch
		endif
	


	rule r_Fallback_attacker = 
			if executing_function(current_layer) != attack then
				switch instruction_pointer(current_layer)
					case 0 : 
						r_Require[false]
				endswitch
			endif
		
		
	
	rule r_Attacker =  
		par
			r_Attack[]
			r_Fallback_attacker[]
		endpar


