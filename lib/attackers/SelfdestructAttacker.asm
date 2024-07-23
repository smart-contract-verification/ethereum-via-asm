module SelfdestructAttacker


import ../solidity/EVMlibrary
import ../asmeta/StandardLibrary


export *


signature:

	controlled input_user : User
	
	static attacker : User
	
	static attack : Function


definitions:

	rule r_Attack =
		if executing_function(current_layer) = attack then
			switch instruction_pointer(current_layer)
				case 0 : 
					par
						input_user := random_user
						instruction_pointer(current_layer) := instruction_pointer(current_layer) + 1
					endpar
				case 1 : 
					r_Selfdestruct[input_user]
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


