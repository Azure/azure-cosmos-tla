# High-level TLA+ specifications for the five consistency levels offered by Azure Cosmos DB

We describe the consistency guarantees provided to the clients by [Azure Cosmos DB](http://cosmosdb.com). Customers of Cosmos DB can associate any number of Azure regions (50+ at the time of writing) to their Cosmos datbase, at any time. The clients can read and write locally from any of the regions associated with the given Cosmos database.

Cosmos DB allows developers to choose between [five well-defined consistency models](https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels) along the consistency spectrum – *strong*, *bounded staleness*, *session*, *consistent prefix* and *eventual*. Cosmos DB has operationalized and exposed them to developers with clear semantics, performance/availability tradeoffs and backed by comprehensive [Service Level Agreements (SLAs)](https://azure.microsoft.com/en-us/support/legal/sla/cosmos-db/). Informally, the five consistency models are described as below.


<style type="text/css">
.tg  {border-collapse:collapse;border-spacing:0;}
.tg td{padding:10px 5px;border-style:solid;border-width:1px;overflow:hidden;word-break:normal;border-color:black;}
.tg th{padding:10px 5px;border-style:solid;border-width:1px;overflow:hidden;word-break:normal;border-color:black;}
.tg .tg-0pky{border-color:inherit;text-align:left;vertical-align:top}
.tg .tg-0lax{text-align:left;vertical-align:top}
</style>
<table class="tg">
  <tr>
    <th class="tg-0pky">Consistency Level</th>
    <th class="tg-0pky">Guarantees</th>
  </tr>
  <tr>
    <td class="tg-0pky">Strong</td>
    <td class="tg-0pky">Linearizable reads</td>
  </tr>
  <tr>
    <td class="tg-0pky">Bounded Staleness</td>
    <td class="tg-0pky">Consistent Prefix. Reads lag behind writes by k prefixes or t interval</td>
  </tr>
  <tr>
    <td class="tg-0pky">Session</td>
    <td class="tg-0pky">Consistent Prefix. Monotonic reads, monotonic writes, read-your-writes, write-follows-reads</td>
  </tr>
  <tr>
    <td class="tg-0pky">Consistent Prefix</td>
    <td class="tg-0pky">Updates returned are some prefix of all the updates, with no gaps</td>
  </tr>
  <tr>
    <td class="tg-0pky">Eventual</td>
    <td class="tg-0pky">Eventual</td>
  </tr>
</table>

Describing the consistency levels in English is prone to errors due to the ambiguity of natural language and the hand waving and generalizations involved.  In this document, we use [TLA+ specification language](http://lamport.azurewebsites.net/tla/tla.html) to specify the consistency guarantees precisely. TLA+ is a tool for specifying distributed algorithms/protocols mathematically and model checking them for correctness. The Cosmos DB engineering team heavily relies on TLA+ for specifying distributed algorithms and protocols mathematically and model checking them for correctness to verify the design decisions and address the corner cases induced by concurrency and faults.

Although Cosmos DB is a globally distributed database, it provides the user with a single logical system image of all of their globally distributed data. The specifications we provide in this document focus on the clients' interactions with their globally distributed Cosmos DB database as a single logical entity by performing writes and reads, based on the consistency level specified. We refrain from modeling the Cosmos DB internals (as that is not very useful/relevant for the Cosmos DB users), and model a user's Cosmos DB database as a single system image, hiding the underlying global distribution/replication among the regions. 

To simplify the exposition of the consistency guarantees given to the clients, we provide three simple scenarios accompanied by their TLA+ specifications. The first two (Scenario 1 and Scenario 2), we consider a single client interacting with the Cosmos database. These examples also give a gentle introduction to TLA+ ---in this case, more accurately, to its companion language PlusCal, which provides a pseudocode-like interface to the TLA+ specifications.

In the final example (the general model), we present our TLA+/PlusCal specification of the general model of Cosmos DB, where multiple clients across different regions put Cosmos DB to the test with respect to the consistency guarantees it provides in the presence of concurrent read and writes.

* [Scenario 1: TLA+ for a client writing incremented counter values](scenario1/README.md)

* [Scenario 2: TLA+ for a client Reading, incrementing, writing-back counter values](scenario2/README.md) 

* [The general model: TLA+ for the general model with multiple clients operating on a globally distributed Cosmos database](general-model/README.md)




  
 