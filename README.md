# ufrn_evp_work2
A work for Especificação e Verificação de Programas class at Universidade Federal do Rio Grande do Norte.

# Steps to get every thing working
1. install openjml's plugin on eclipse:
	Click top menu: Help > Install New Software.
	Copy and past this link in work with field and press enter: http://jmlspecs.sourceforge.net/openjml-updatesite.
	Select all the boxes that appears and finish installation.
	
2. configure your project to rum with jre 1.8:
	right click in your project > properties > left menu 'java build path' > select tab libraries in right page
	> click JRE System Libraries > click 'edit' on right side > select Workspace default JRE (jre1.8.0_171).
	~ I don't know if it works with jre1.7, it may work.
	click finish > click apply and close.

3. download z3 solver version 4.3.2 x86 or x64 according to your machine (only version that works for me) https://github.com/Z3Prover/z3/releases and extract any where (lets call this folder 'folder'). 

4. configure eclipse to use the downloaded solver:
	Top menu > Window > Preferences >  open OpenJML in left menu > click OpenJML Solvers.
	At z3_4_3 select 'external' and click 'Browser' to select 'folder/z3-4.3.2-x64-win/bin/z3.exe'.
	At the top of this window click 'Edit solver list', select 'z3_4_3' and click 'Up' until it be at the top, and click 'ok'.
	Click apply and close.

5. Test if you sintaxis and static checking is working!
	
	