# Ethereum Via ASM

The "Ethereum Via ASM" repository facilitates the modeling of Ethereum smart contracts (SCs) by leveraging Abstract State Machines (ASMs). This repository includes libraries that model the core Ethereum Virtual Machine (EVM) mechanisms using defined rules and functions. Additionally, it features a set of example smart contracts gathered from diverse sources.

## Requirements
- Eclipse IDE
- ASM symbolic executor ([GitHub](https://github.com/constructum/asm-symbolic-execution))

## Installation
- ASMETA installation : 
  - Go to *help -> Install New Software ...*
  - *Add* the following link https://raw.githubusercontent.com/asmeta/asmeta_update_site/master and *Select All*
- *Clone* and *Import* this repository as an *existing Eclipse projects*

## Repository Structure
```md
    ├── examples
    │   ├── AirdropAttack
    │   │   ├── Airdrop.sol
    │   │   ├── Airdrop_V1.asm
    │   │   ├── Airdrop_V2.asm
    │   │   └── Airdrop_V3.asm
    │   ├── AnalisysResults.md
    │   ├── Auction
    │   │   ├── Auction.asm
    │   │   ├── Auction.sol
    │   │   ├── Auction_V1.asm
    │   │   ├── Auction_V2.asm
    │   │   ├── Auction_inv.asm
    │   │   └── scenario
    │   │       └── inv_1.avalla
    │   ├── Baz
    │   │   ├── Baz_V1.asm
    │   │   └── baz.sol
    │   ├── Crowdfund
    │   │   ├── Crowdfund_V1.asm
    │   │   ├── Crowdfund_V2.asm
    │   │   └── crowdfund.sol
    │   ├── Kotet
    │   │   ├── Kotet.sol
    │   │   ├── Kotet_V1.asm
    │   │   └── Kotet_V2.asm
    │   └── StateBasedDAO
    │       ├── StateDAO.sol
    │       ├── StateDAO_V1.asm
    │       └── StateDAO_V2.asm
    └── lib
        ├── asmeta
        │   ├── CTLlibrary.asm
        │   └── StandardLibrary.asm
        └── solidity
            ├── EVMLibrary.asm
            └── EVMLibrarySymbolic.asm
```

The repository is structured into two main folders: **examples** and **lib**. The examples folder contains original contracts, their corresponding models, and version variations. <br> 
The **lib** folder houses necessary libraries for executing  ASMs within the **asmeta** subfolder, and for modeling SCs within the **solidity** subfolder. Within the **examples** folder, the **AnalysisResults.md** file stores the results of symbolic execution performed on each model and its versions.

## Appendix
![Appendix](ABZ2025_Appendix.pdf)