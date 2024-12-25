int n = ...; // INPUT: numero di squadre, =36 per CL
int d = ...; // INPUT: numero di turni, =8 per CL

assert (n % 2) == 0;
assert (d % 2) == 0;

range TEAMS = 1..n;
range DAYS = 1..d;


//INPUT: nomi delle squadre
string names [TEAMS] = ...;

//INPUT: ranking delle squadre
string ranking[TEAMS] = ...;

//INPUT: nazionalità delle squadre
string country[TEAMS] = ...;

//INPUT: città in cui giocano le squadre
string city[TEAMS] = ...;

//insieme delle fasce
 {string} ranking_names = ...;

assert(d % card(ranking_names)) == 0;

//insieme delle nazionalità
{string} country_names= ...;

//indisponibilità stadio, la inizializzo
int u[TEAMS][DAYS] = ...;


//popolarità delle squadre, la inizializzo
int b[TEAMS] = ...;


//INIZIALIZZO distanza tra due città con una formula approssimativa
//nota: la formula non approssima molto bene per distanze corte come queste


float R=6371.0; //raggio della terra in km

float latitudine[TEAMS]=...; //in gradi
float longitudine[TEAMS]=...; //in gradi

float lat[TEAMS]; //in radianti, da calcolare
float lon[TEAMS]; //in radianti, da calcolare

execute {
  for(var i in TEAMS)
    lat[i] = latitudine[i] * 3.141593 / 180.0;
    lon[i] = longitudine[i] * 3.141593 / 180.0;
}

float distance[TEAMS][TEAMS]; //da calcolare con formula approssimativa

execute {
  for(var i in TEAMS)
  for(var j in TEAMS)
    distance[i][j] = Math.acos (Math.sin(lat[i])*Math.sin(lat[j])+Math.cos(lat[i])*Math.cos(lat[j])*Math.cos(lon[j]-lon[i]))*R;
}




//VARIABILI DECISIONALI

dvar boolean x[TEAMS][TEAMS][DAYS]; /*variabile decisionale booleana
uguale a 1 se la squadra i (in casa) incontra j (fuori casa) nella giornata d ; 0 altrimenti*/

// variabile booleana che indica se la squadra i gioca in casa nella giornata p o meno
dvar boolean h[TEAMS][DAYS];

//variabili per conteggio vincolo soft S1
dvar boolean d_S1[TEAMS][DAYS];

//variabili per conteggio vincolo soft S2
dvar boolean d_S2h[TEAMS][DAYS];
dvar boolean d_S2a[TEAMS][DAYS];

//variabili per conteggio vincolo soft S3
dvar boolean d_S3[TEAMS][ranking_names];

//variabile per conteggio vincolo soft S4
dvar int+ d_S4;

//variabili per conteggio vincolo soft S5
dvar boolean d_S5[TEAMS][country_names];

//variabili per conteggio vincolo soft S6
dvar boolean d_S6[DAYS];

//variabili per conteggio vincolo soft S7
dvar boolean d_S7[TEAMS];

//espressione per calcolo distanza totale
dexpr float dist = sum (p in DAYS, i in TEAMS, j in TEAMS : j < i) distance[i][j] * (x[i][j][p] + x[j][i][p]) ;

//distanza media
dexpr float dist_avg = (sum (i in TEAMS, j in TEAMS : i != j) distance[i][j]) / (n-1) / (n-1);

float M = 1000.0; // big number utile per il vincolo delle distanze. Ogni mille km scatta una penalità

//FUNZIONE OBIETTIVO: minimizzare penalità
 minimize sum(i in TEAMS, p in DAYS) d_S1[i][p] + sum (p in DAYS, i in TEAMS) (d_S2h[i][p] + d_S2a[i][p])
  + sum (f in ranking_names, i in TEAMS) d_S3[i][f] + 
 sum (n in country_names, i in TEAMS)d_S5[i][n] + sum (p in DAYS)d_S6[p] + sum (i in TEAMS)d_S7[i]
  + d_S4;



//VINCOLI

//VINCOLI HARD

subject to {
 
 
  //H1.ogni squadra gioca contro un'altra AL MASSIMO una volta - SORTEGGIO
  forall(i in TEAMS, j in TEAMS : i<j)
    sum(p in DAYS) (x[i][j][p] + x[j][i][p]) <= 1;
   
  //H2.ogni squadra gioca una volta in ogni periodo - SCHEDULAZIONE
  forall(i in TEAMS, p in DAYS)
    sum(j in TEAMS : j != i) (x[i][j][p] + x[j][i][p]) == 1;
  
  //H3.attivo variabile in casa - SCHEDULAZIONE
  forall (i in TEAMS, p in DAYS)
    h[i][p] == sum(j in TEAMS : j !=i ) x[i][j][p];
   
  //H3.metà delle partite devono essere in casa - SCHEDULAZIONE
  forall(i in TEAMS)
    sum(p in DAYS) h[i][p] == d div 2;
   
   //H3.attivo variabile fuori casa - SCHEDULAZIONE
  forall (i in TEAMS, p in DAYS)
    1 - h[i][p] == sum(j in TEAMS : j !=i ) x[j][i][p];
   
  /* //H3.metà delle partite devono essere fuori casa - SCHEDULAZIONE
  forall(i in TEAMS)
    sum(p in DAYS) a[i][p] == d div 2;  
    */
   
   //H8.massimo due partite di fila in casa o fuori - SCHEDULAZIONE - X
   forall (i in TEAMS, p in 1..(card(DAYS)-2)) h[i][p] + h[i][p+1] + h[i][p+2] <= 2;
   forall (j in TEAMS, p in 1..(card(DAYS)-2)) 1 - h[j][p] + 1 - h[j][p+1] + 1 - h[j][p+2] <= 2;  
   
   //H5.ogni squadra gioca contro d/f squadre per fascia - SORTEGGIO
   forall (i in TEAMS, f in ranking_names)
     sum (p in DAYS, j in TEAMS : ranking[j] == f && j != i) (x[i][j][p] + x[j][i][p]) == d div card(ranking_names);
   
   //H4.squadre che hanno la stessa città non possono giocare in casa contemporanemanete - SCHEDULAZIONE
   forall (p in DAYS, i in TEAMS, j in TEAMS : i<j && city[i] == city[j])
     h[i][p] + h[j][p] <= 1;
   
   //H7.non sono permessi derby nazionali - SORTEGGIO - X
   forall (i in TEAMS, j in TEAMS, p in DAYS : i<j && country[i] == country[j])
     x[i][j][p] + x[j][i][p] == 0;
  
  //H9.Le prime due giornate e le ultime due giornate, per ogni squadra, devono giocarsi in alternanza casa / fuori casa (o fuori casa / casa) - SCHEDULAZIONE -X
   forall (i in TEAMS)
     h[i][1]+h[i][2] == 1;
   forall (i in TEAMS)
     1 - h[i][1] + 1 - h[i][2] == 1;
   forall (i in TEAMS)
     h[i][card(DAYS)-1]+h[i][card(DAYS)] == 1;
   forall (i in TEAMS)
    1 - h[i][card(DAYS)-1] + 1 - h[i][card(DAYS)] == 1;
   
   
   //H10.Ogni squadra deve sfidare al massimo due squadre della stessa nazione - SORTEGGIO - X
   forall (i in TEAMS, n in country_names)
     sum (p in DAYS, j in TEAMS : country[j] == n && j != i) (x[i][j][p] + x[j][i][p]) <= 2;
  
     
   //H6.Ogni squadra gioca un uguale numero di partite in casa e fuori casa contro squadre della stessa fascia (una e una) - SCHEDULAZIONE - X
   forall (i in TEAMS, f in ranking_names)
     sum (p in DAYS, j in TEAMS : ranking[j] == f && j != i) x[i][j][p] == sum (p in DAYS, j in TEAMS : ranking[j] == f) x[j][i][p];

//VINCOLI SOFT

   //S1. evitare di schedulare partite in stadi in cui è stata comunicata una possibile indisponibilità degli stadi
   // capacity constraint - SCHEDULAZIONE
   
   forall (i in TEAMS, p in DAYS : u[i][p] == 1)
     h[i][p] - d_S1[i][p] <= 0;
 

   //S2. break constraint - SCHEDULAZIONE
    forall (i in TEAMS, p in 2..card(DAYS))
     h[i][p-1] + h[i][p] - d_S2h[i][p] <= 1;
   forall (i in TEAMS, p in 2..card(DAYS))
     1 - h[i][p-1] + 1 - h[i][p] - d_S2a[i][p] <= 1;  
 
     
     
    //S3. fairness: calendario di ogni squadra suddiviso in due metà in base alle fasce - SCHEDULAZIONE
     forall (i in TEAMS, f in ranking_names)
       (sum(p in 1..card(DAYS) div 2, j in TEAMS : ranking[j]==f  && j !=i)
       (x[i][j][p] + x[j][i][p])) + d_S3[i][f] >=1;
         
   
    //S4. distanza. La distanza totale deve essere più corta della media. Ogni 1000 km penalità - SORTEGGIO
      dist - M*d_S4 <= 0.9*dist_avg*d*(n/2);
   
    //S5. nazioni diverse - SORTEGGIO
     forall (i in TEAMS, n in country_names)
      (sum (p in DAYS, j in TEAMS : country[j] == n && j != i) (x[i][j][p]+x[j][i][p])) - d_S5[i][n] <=1;
    
    //S6. Schedulare almeno un big match per giornata - SCHEDULAZIONE ( + SORTEGGIO per massimizzare big match)
     forall (p in DAYS)
       (sum(i in TEAMS, j in TEAMS : j>i && b[i]==1 && b[j]==1) (x[i][j][p] + x[j][i][p])) + d_S6[p] >=1;
   
    //S7. visibilità per le squadre "non popolari" - SORTEGGIO
     forall (i in TEAMS : b[i] == 0)
       (sum (p in DAYS, j in TEAMS : j != i && b[j]==1) (x[i][j][p] + x[j][i][p])) + d_S7[i] >=1;
   
}

/// Per stampare un output
tuple Solution{
  int week;
  string team1;
  string fascia1;
  string team2;
  string fascia2;
};

sorted {Solution} solution = {<p,
                               names[i], ranking[i],
                               names[j], ranking[j]>  |
                               i in TEAMS, j in TEAMS, p in DAYS : x[i][j][p] == 1};
                               
execute DEBUG {
  writeln("dist " + dist);
  writeln("dist_avg_partita singola " + dist_avg);
  writeln("dist_avg tot " + dist_avg*d*n/2);
  writeln("dist_avg tot 0,9 " + 0.9*dist_avg*d*n/2);
  var week = 0;
  for (var s in solution) {
    if (s.week != week) {
      week = s.week;
      writeln("================================");
      writeln("On week " + week);
    }
      writeln("Home: " + s.team1 + "(Fascia " + s.fascia1 +  ") - Away: " + s.team2 + "(Fascia " + s.fascia2 +  ")")          
    }
 

}