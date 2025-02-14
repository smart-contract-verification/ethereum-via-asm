pragma solidity ^0.8.13;


contract Airdrop {
    mapping (address => uint256) private userBalances;
    mapping (address => bool) private receivedAirdrops;

    uint256 public airdropAmount;

    function receiveAirdrop() external {
        
        require(!receivedAirdrops[msg.sender], "You already received an Airdrop");

        (bool succ, ) = msg.sender.call("");
        
        // Mint Airdrop
        userBalances[msg.sender] += airdropAmount;
        receivedAirdrops[msg.sender] = true;
    }
}