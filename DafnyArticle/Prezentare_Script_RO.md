# Script prezentare: Verificarea formală a bytecode-ului EVM în Dafny

**Durată estimată: ~7 minute**

---

## Introducere și contextul problemei (1 minut 30 secunde)

Această prezentare tratează verificarea formală a bytecode-ului Ethereum, o lucrare realizată de echipa Consensys folosind limbajul de verificare Dafny.

Când un dezvoltator scrie un smart contract, procesul standard include mai multe etape de validare. Codul sursă, scris în Solidity sau Vyper, este analizat de auditori, testat extensiv, și uneori verificat formal. Toate aceste eforturi de securitate se concentrează pe artefactul sursă, pe codul pe care dezvoltatorul îl scrie și îl poate citi.

Problema fundamentală este că Ethereum nu execută cod sursă. Mașina virtuală Ethereum primește și execută bytecode, o secvență de bytes generată de compilator prin transformarea codului sursă. Între ceea ce se verifică și ceea ce se execută există un program intermediar complex: compilatorul.

Compilatorul Solidity conține aproximativ 500.000 de linii de cod C++. Compilatorul Vyper este scris în Python. Niciun compilator major pentru Ethereum nu este verificat formal, ceea ce înseamnă că nu există garanții matematice că transformarea din cod sursă în bytecode păstrează comportamentul intenționat.

Această situație creează un decalaj de verificare: chiar dacă codul sursă este demonstrat corect, bytecode-ul executat poate conține erori introduse de compilator.

---

## Exemple concrete de vulnerabilități cauzate de compilatoare (1 minut 30 secunde)

Pentru a ilustra gravitatea acestei probleme, există cazuri documentate în care bug-uri de compilator au cauzat pierderi financiare majore.

În iulie 2023, platforma Curve Finance a pierdut 26 de milioane de dolari într-un atac care a exploatat un bug în compilatorul Vyper. Contractele afectate foloseau decoratorul nonreentrant, o protecție standard care ar trebui să prevină apelurile recursive. Când o funcție marcată cu acest decorator apelează un contract extern, iar acel contract încearcă să apeleze înapoi funcția originală, al doilea apel ar trebui să eșueze. Dezvoltatorii au aplicat această protecție corect. Auditorii au verificat că decoratorul era prezent. La nivel de cod sursă, totul era în regulă.

Bug-ul se afla în compilatorul Vyper, în versiunile 0.2.15 până la 0.3.0. Compilatorul genera bytecode în care ordinea operațiilor de verificare și setare a lock-ului era inversată. Un atacator putea astfel să reintre în funcție deși protecția era specificată în cod.

Un caz similar s-a întâmplat cu Solidity în 2022. Optimizer-ul, componenta care îmbunătățește eficiența bytecode-ului generat, efectuează o operație numită eliminarea codului mort, prin care înlătură operații ale căror rezultate nu sunt folosite. Un bug în această analiză a cauzat clasificarea greșită a unor scrieri în storage ca fiind inutile, deși erau de fapt necesare. Codul sursă conținea aceste scrieri, dar bytecode-ul compilat nu le mai includea.

Aceste bug-uri au o caracteristică comună: nu pot fi detectate prin analiza codului sursă, deoarece codul sursă exprimă corect comportamentul intenționat.

---

## Soluția propusă: semantică formală a EVM-ului în Dafny (1 minut)

Soluția propusă de echipa Consensys este verificarea directă a bytecode-ului. Proiectul Dafny-EVM oferă o specificație formală și executabilă a mașinii virtuale Ethereum care permite demonstrarea proprietăților despre bytecode, nu despre cod sursă.

Dafny este un limbaj de programare cu verificare automată dezvoltat de Microsoft Research. Sintaxa sa seamănă cu cea a limbajelor imperative obișnuite, dar permite adnotarea funcțiilor cu precondiții și postcondiții. Verificatorul Dafny, folosind solver-ul SMT Z3, demonstrează automat că aceste condiții sunt satisfăcute pentru toate inputurile posibile.

Comparativ cu asistenți de demonstrare precum Coq sau Isabelle, Dafny este mai accesibil pentru programatori, deoarece demonstrațiile manuale sunt necesare doar în cazuri complexe. Pentru majoritatea specificațiilor, verificarea se face automat.

Specificația Dafny-EVM este și executabilă, ceea ce înseamnă că poate fi compilată și rulată pentru a executa bytecode real și a compara rezultatele cu testele de referință Ethereum.

---

## Arhitectura mașinii virtuale Ethereum (1 minut 30 secunde)

Pentru a înțelege verificarea bytecode-ului, este necesară o prezentare a arhitecturii EVM.

Mașina virtuală Ethereum este o mașină bazată pe stivă. Spre deosebire de arhitecturile cu registre, EVM-ul nu are registre generale. Toate operațiile folosesc o singură stivă cu maximum 1024 de elemente, fiecare element având 256 de biți.

Pentru a efectua o adunare, de exemplu, se împing cele două valori pe stivă, apoi se execută instrucțiunea ADD care scoate ambele valori de pe stivă, calculează suma, și pune rezultatul înapoi pe stivă. Accesul la elemente mai adânci în stivă se face prin instrucțiuni speciale: DUP pentru duplicare și SWAP pentru interschimbare.

Aritmetica EVM operează pe întregi fără semn de 256 de biți. Când rezultatul unei operații depășește valoarea maximă reprezentabilă, se produce overflow, iar rezultatul se calculează modulo 2 la puterea 256. Acest comportament este specificat în protocolul Ethereum și nu reprezintă un bug.

EVM-ul are două tipuri de spațiu de stocare. Memoria este un array volatil de bytes care se resetează la fiecare tranzacție, iar costul accesului crește pătratic cu dimensiunea. Storage-ul este o mapare persistentă de la chei de 256 de biți la valori de 256 de biți, care rămâne între tranzacții, iar costul scrierii poate ajunge la 20.000 de unități de gas.

Fiecare instrucțiune consumă gas, o unitate de măsură a resurselor computaționale. Instrucțiunea ADD costă 3 gas, în timp ce o scriere în storage poate costa până la 20.000 de gas. Dacă execuția epuizează gas-ul disponibil, mașina virtuală se oprește și toate modificările de stare sunt anulate.

---

## Reprezentarea stării și execuția în Dafny-EVM (1 minut)

În Dafny-EVM, starea completă a mașinii virtuale este reprezentată ca un tip de date algebric care include toate componentele relevante: versiunea protocolului numită fork, contextul tranzacției care conține informații despre apelant și valoarea transferată, starea globală cu toate balanțele și storage-ul conturilor, stiva curentă, memoria, bytecode-ul care se execută, cantitatea de gas rămasă, și program counter-ul care indică instrucțiunea curentă.

Execuția poate produce patru tipuri de rezultate: starea poate rămâne în execuție dacă mai sunt instrucțiuni de procesat, poate termina normal prin instrucțiunile STOP sau RETURN, poate produce o eroare precum epuizarea gas-ului sau underflow de stivă, sau poate intra într-o stare de continuare când așteaptă rezultatul unui apel către alt contract.

Bytecode-ul este o secvență de bytes, iar funcția de execuție citește byte-ul de la poziția curentă a program counter-ului, verifică dacă reprezintă un opcode valid pentru fork-ul curent, deduce costul în gas, și apoi aplică semantica opcode-ului. Un aspect important al designului este separarea semanticii funcționale de contabilitatea gas-ului, ceea ce permite verificarea independentă a corectitudinii computaționale și a costurilor.

---

## Specificarea formală a opcode-urilor (45 secunde)

Fiecare opcode din EVM este definit ca o funcție matematică de la stare la stare, însoțită de o specificație formală.

Luând ca exemplu instrucțiunea ADD, specificația precizează că funcția necesită ca mașina să fie în stare de execuție. Postcondițiile garantează că rezultatul este fie o stare validă, fie specific eroarea de underflow de stivă, că rezultatul este valid dacă și numai dacă existau cel puțin două elemente pe stivă, și că în caz de succes stiva are un element mai puțin decât înainte.

Implementarea verifică dacă stiva are suficiente elemente, extrage cele două valori de pe vârf, calculează suma modulo 2 la puterea 256, și returnează noua stare cu rezultatul pe stivă. Dafny demonstrează automat că implementarea satisface specificația pentru toate inputurile posibile.

---

## Verificarea detecției de overflow (1 minut)

Primul exemplu de verificare din lucrare demonstrează corectitudinea bytecode-ului generat de Solidity pentru detecția overflow-ului la adunare.

Începând cu versiunea 0.8, Solidity generează bytecode care verifică dacă adunarea a produs overflow și, în caz afirmativ, anulează tranzacția. Proprietatea de demonstrat este că bytecode-ul face revert dacă și numai dacă suma matematică a celor două numere depășește valoarea maximă reprezentabilă pe 256 de biți.

Fundamentul matematic al detecției este următorul: pentru două numere x și y, overflow-ul a avut loc dacă și numai dacă rezultatul înfășurat modulo 2 la puterea 256 este mai mic decât x. Această echivalență se poate demonstra prin faptul că, în caz de overflow, rezultatul înfășurat este x plus y minus 2 la puterea 256, care este strict mai mic decât x deoarece y este pozitiv dar mai mic decât 2 la puterea 256.

Bytecode-ul generat de Solidity duplică una dintre valori, efectuează adunarea, compară rezultatul cu valoarea originală, și sare la secvența de revert dacă comparația indică overflow. Metoda de verificare din Dafny execută acest bytecode cu inputuri simbolice și demonstrează că postcondițiile sunt satisfăcute pentru toate cele 2 la puterea 512 perechi posibile de valori, nu prin testare exhaustivă, ci prin demonstrație simbolică.

---

## Verificarea terminării buclelor (45 secunde)

Al doilea exemplu demonstrează terminarea unei bucle care iterează de un număr fix de ori.

Bytecode-ul împinge un contor pe stivă, apoi intră într-o buclă care verifică dacă contorul este nenul, și dacă da, îl decrementează și sare înapoi la începutul buclei. Când contorul ajunge la zero, execuția continuă și termină normal.

Pentru a demonstra terminarea, Dafny folosește o clauză numită decreases care specifică o expresie ce scade strict la fiecare iterație și este mărginită inferior. În acest caz, expresia este valoarea contorului de pe stivă, care scade de la valoarea inițială c la zero. Deoarece valorile sunt naturale și expresia scade la fiecare iterație, bucla trebuie să termine.

O variabilă ghost, vizibilă doar verificatorului, urmărește numărul de iterații efectuate, iar la finalul execuției se demonstrează că au avut loc exact c iterații. Verificarea acoperă toate valorile lui c între 0 și 255.

---

## Verificarea corectitudinii optimizărilor de compilator (45 secunde)

Al treilea exemplu verifică o optimizare pe care compilatoarele o pot aplica asupra bytecode-ului.

Secvența originală constă dintr-o instrucțiune SWAP urmată de n plus 1 instrucțiuni POP. SWAP-ul rearanjează elementele de pe stivă, iar POP-urile le elimină. Optimizarea observă că elementele rearanjate de SWAP vor fi oricum eliminate, deci SWAP-ul poate fi înlăturat, lăsând doar cele n plus 1 instrucțiuni POP.

Verificarea pornește două instanțe ale mașinii virtuale din aceeași stare inițială. Una execută secvența optimizată, cealaltă secvența originală. Asertiunile verifică că ambele instanțe ajung la aceeași stivă finală și că versiunea optimizată consumă mai puțin gas.

Dafny verifică această proprietate pentru toate valorile lui n între 1 și 16 și pentru toate configurațiile valide de stivă.

---

## Rezultate și limitări (30 secunde)

Specificația Dafny-EVM trece 6.618 din 8.189 teste comune Ethereum, reprezentând aproximativ 81 la sută. Eșecurile se datorează contractelor precompilate și funcționalităților specifice anumitor fork-uri care nu sunt încă implementate.

Limitările includ scalabilitatea, deoarece contractele complexe cu multe bucle necesită invarianți specificați manual. Apelurile externe introduc incertitudine deoarece codul contractului apelat nu este cunoscut la momentul verificării. De asemenea, mapările din Solidity folosesc funcția hash keccak256 pentru calculul sloturilor de storage, iar demonstrarea non-coliziunii presupune rezistența criptografică a funcției hash.

În ciuda acestor limitări, proiectul demonstrează că verificarea formală a bytecode-ului EVM este fezabilă și poate oferi garanții despre comportamentul real al smart contract-urilor.
