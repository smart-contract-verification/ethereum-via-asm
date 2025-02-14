contract KotET {
    address payable public king;
    uint public claimPrice = 1;
    address owner;
    
    fallback () external payable {
        require(msg.value < claimPrice);

        king.send(claimPrice + 2);
        claimPrice = claimPrice + 1;
        king = payable(msg.sender);
    }
}