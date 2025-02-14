pragma solidity ^0.4.20;

contract Auction {
  address currentFrontrunner;
  address owner;
  uint currentBid;
  
  function destroy() {
    selfdestruct(owner);
  }
  function bid() payable {
    require(msg.value > currentBid);  
    if (currentFrontrunner != 0) {
      require(currentFrontrunner.send(currentBid));
      }  
    currentFrontrunner = msg.sender;
    currentBid         = msg.value;
  }
}