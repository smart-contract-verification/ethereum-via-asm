
contract StateDAO {

    enum States {
        InTransition,
        InitialState 
    }

    mapping (address => uint) customer_balances;
    States state = States.InitialState;

    function deposit () public payable {
        require(state == States.InitialState);
        state = States.InTransition;
        require(address(this).balance < 3 ether);
        customer_balances[msg.sender]=msg.value;
        state = States.InitialState; 
    }


    function withdraw () public returns (bool val) {
        require(state == States.InitialState);
        state = States.InTransition; 
        require(customer_balances[msg.sender] > 0);
        (bool res, ) = msg.sender.call{value: customer_balances[msg.sender]}("");
        if (res) {
            customer_balances[msg.sender] = 0;
            return true;
        }
        state = States.InitialState; 
    }

}