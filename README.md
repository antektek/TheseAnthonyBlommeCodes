# Thèse Anthony Blomme Codes

## minisat-cache

Ce dossier contient les codes utilisés pour les expérimentations concernant le système de cache.
Un code pour l'architecture DPLL et un autre pour l'architecture CDCL sont fournis.
Le dossier *core* contient les fichiers principaux.


### Compilation

Pour compiler ces programmes, il faut d'abord exporter la variable MROOT avec le chemin de l'endroit où se trouvent le dossier *core* :

```
export MROOT=<minisat-dpll/cdcl>
```

Ensuite, à l'intérieur du dossier *core*, il est possible d'utiliser le Makefile fourni :

```
cd core
make
```

L'exécutable *minisat* est alors créé et celui-ci peut être lancé de la manière suivante :

```
./minisat file.cnf
```

Ce programme utilise régulièrement un dossier intitulé *cache* pour stocker divers fichiers CSV représentant les formules mises en cache.
Ce dossier doit donc exister à l'intérieur du dossier *core*.
De plus, le programme fait régulièrement appel au [Glasgow Subgraph Solver](https://github.com/ciaranm/glasgow-subgraph-solver).
Ce programme doit donc être préalablement compilé et son exécutable doit exister dans le dossier *core*.


### Options

Dans le fichier *Solver.h*, il est possible de modifier un certain nombre d'options :

* allCache : Afficher dans le résultat toutes les entrées de cache créées. Si cette option est à false, on n'affiche que les entrées qui ont détecté au moins un isomorphisme.

* forceOrder : Forcer l'ordre des décisions dans le solveur. Si plus aucune décision n'est disponible, on utilise l'heuristique de MiniSat. Le programme lit le contenu du fichier *order.txt* avant le début de la recherche.

* useRestarts : Activer ou désactiver les restarts de la version CDCL. Cette option a toujours été à false dans les diverses expérimentations.
    
* makeDot : Représenter l'arbre de la recherche sous la forme d'un graphe au format DOT. Le résultat est stocké dans le fichier *file.cnf.dot*.

* clearCache : Supprimer les fichiers CSV utilisés pour stocker les entrées de cache.

* explorePrunedBranches : Explorer les branches élaguées au cours de la recherche. Si cette opton est à true, on continue la recherche même lorsqu'une entrée de cache a été reconnue. Cette option a été utilisée lors des expérimentations sur le pouvoir de compression.

* acceptAfterHit : On continue de créer des entrées de cache lors de l'exploration des branches élaguées. Cette option n'a d'effet que si l'option *explorePrunedBranches* est à vrai.

* showPrunedBranches : Représenter les branches élaguées dans le fichier DOT (celles-ci sont représentées en gris). Cette option n'a d'effet que si l'option *explorePrunedBranches* est à vrai.

* generalizedIso : Utiliser la détection d'isomorphismes généralisés. Si cette option est à false, on utilise les isomorphismes classiques.

* usePrecompiledCache : Utiliser uniquement un cache pré-compilé. Le programme lit le fichier *precompile.txt* avant le début de la recherche. Celui-ci doit contenir les chemins des formules à créer dans le cache. Chaque ligne doit correspondre à un fichier décrivant une formule au format DIMACS (sans commentaire et sans préfixe). Cette option a été utilisée pour tester un cache pré-compilé avec des problèmes de pigeons.

* printTrace : Afficher certaines étapes de la recherche. Cette option a été utilisée lors des expérimentations sur la taille de l'encodage.


## pigeon-detection

Ce dossier contient les codes utilisés pour les expérimentations concernant la détection de problèmes de pigeons.
Pour chaque partie (détection pure et échantillonnage), deux codes sont fournis.
Un premier avec lequel les expérimentations ont été réalisées et un second implémentant des watched literals.


### Utilisation

Les programmes fournis peuvent être lancés en faisant appel à python3 :

```
python3 pigeonPur.py file.cnf
```
