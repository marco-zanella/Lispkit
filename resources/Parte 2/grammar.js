function Terminal(name){
 this.name = name;
}



function NonTerminal(name){
 this.name = name;
 this.first = new Array();
 this.follow = new Array();
 
 this.addFirst = function(terminal){
  for(var i in terminal){
   this.first.push(terminal[i]);
  }
 }
 
 this.addFollow = function(terminal){
  for(var i in terminal){
   this.follow.push(terminal[i]);
  }
 }
}



function G(terminals, nonterminals){
 this.T = new Array();
 this.NT = new Array();
 
 for(var i in terminals){
  this.T[terminals[i]] = new Terminal(terminals[i]);
 }
 
 for(var i in nonterminals){
  this.NT[nonterminals[i]] = new NonTerminal(nonterminals[i]);
 }
}
