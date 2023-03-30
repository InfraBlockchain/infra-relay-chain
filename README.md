# InfraBlockspace
 
> Substrate-based heterogenous and interoperable blockchain focusing on enterprise
> Aiming for tokenless blockchain network with using Proof-of-Transaction consensus mechanism 

![](https://i.imgur.com/L5ekohW.jpg)


인프라 블록스페이스(Relaychain)은 각기 다른 역할을 수행하는 블록체인(Parachain)을 연결하여 여러 블록들이 병렬적으로 finalize 될 수 있는 스페이스를 제공한다. 인프라 블록 스페이스의 아키텍처는 Relaychain(**Infrablockspace**)와 Parachain(**InfraBlockchain**)으로 구성되어 있다. 

#### Infrablockspace
- Infrablockchain 이 생성한 블록을 검증하고 finalize 하는 역할을 수행
- Tokenless 네트워크로 PoT([Proof-of-Transaction](https://hackmd.io/NE01Kwp5QD29eQn4J8dXtA?view#Proof-of-Transaction)) 에 의해 validator(Block Producer) 선출

#### Infrablockchain
- **Infrablockspace** 에 연결되어 shared security 를 형성
- Relaychain 에 synchronous 하게 블록이 backing 되어 Relaychain 블록 타임(T) + Parachain 블록 타임(T') 뒤에 블록 형성.
- [Asynchrnous Backing](https://github.com/paritytech/polkadot/issues/3779)

인프라 블록스페이스의 가장 큰 특징은 토큰이 없는 네트워크이며 독자적인 컨센서스 알고리즘인 ***Proof-of-Transaction*** 을 통해 네트워크를 구축하고자 한다.
