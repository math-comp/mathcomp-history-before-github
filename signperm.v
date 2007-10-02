<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE html
	PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
	"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">

<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en   ">

  <head>
	<meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
	<title>InriaGforge: CoqFiniteGroups: SCM Repository</title>
	<link rel="icon" type="image/x-icon" href="/favicon.ico" />
	<link rel="alternate" title="InriaGforge - Project News Highlights RSS" href="/export/rss_sfnews.php" type="application/rss+xml"/>
	<link rel="alternate" title="InriaGforge - Project News Highlights RSS" href="/export/rss20_news.php" type="application/rss+xml"/>
	<link rel="alternate" title="InriaGforge - New Projects RSS" href="/export/rss_sfprojects.php" type="application/rss+xml"/>
	<script language="JavaScript" type="text/javascript">
	<!--
	function admin_window(adminurl) {
		AdminWin = window.open( adminurl, 'AdminWindow','scrollbars=yes,resizable=yes, toolbar=yes, height=400, width=400, top=2, left=2');
		AdminWin.focus();
	}
	function help_window(helpurl) {
		HelpWin = window.open( helpurl,'HelpWindow','scrollbars=yes,resizable=yes,toolbar=no,height=400,width=400');
	}
	// -->
		</script>

<style type="text/css">
	<!--
	BODY {
		margin-top: 3;
		margin-left: 3;
		margin-right: 3;
		margin-bottom: 3;
		background-color: #5651a1;
	}
	ol,ul,p,body,td,tr,th,form { 
				font-family: Arial, Helvetica, sans-serif; 
				font-size:small;
				color: #333333; 
	}

	h1 { font-size: x-large; font-family: Arial, Helvetica, sans-serif; }
	h2 { font-size: large; font-family: Arial, Helvetica, sans-serif; }
	h3 { font-size: medium; font-family: Arial, Helvetica, sans-serif; }
	h4 { font-size: small; font-family: Arial, Helvetica, sans-serif; }
	h5 { font-size: x-small; font-family: Arial, Helvetica, sans-serif; }
	h6 { font-size: xx-small; font-family: Arial, Helvetica, sans-serif; }

	pre,tt { font-family: courier,sans-serif }

	a:link { text-decoration:none; color: #0000be }
	a:visited { text-decoration:none; color: #0000be }
	a:active { text-decoration:none }
	a:hover { text-decoration:underline; color:red }

	.titlebar { color: black; text-decoration: none; font-weight: bold; }
	a.tablink { color: black; text-decoration: none; font-weight: bold; font-size: x-small; }
	a.tablink:visited { color: black; text-decoration: none; font-weight: bold; font-size: x-small; }
	a.tablink:hover { text-decoration: none; color: black; font-weight: bold; font-size: x-small; }
	a.tabsellink { color: #0000be; text-decoration: none; font-weight: bold; font-size: x-small; }
	a.tabsellink:visited { color: #0000be; text-decoration: none; font-weight: bold; font-size: x-small; }
	a.tabsellink:hover { text-decoration: none; color: #0000be; font-weight: bold; font-size: x-small; }
		-->
</style>
<link rel="stylesheet" type="text/css" href="/plugins/scmcvs/cvsweb/css/cvsweb.css" /><link rel="stylesheet" type="text/css" href="/plugins/scmsvn/viewcvs/styles.css" /></head>

<body>

<table border="0" width="100%" cellspacing="0" cellpadding="0">

	<tr>
		<td><a href="/"><img src="/themes/inria/images/logo.png" border="0" alt="" width="227" height="60" /></a></td>
		<td>
		<form action="/search/" method="get">
		<table border="0" cellpadding="0" cellspacing="0">
		<tr><td>
		<div align="center" style="font-size:smaller"><select name="type_of_search"><option value="soft">Software/Group</option>
<option value="people">People</option>
<option value="skill">Skill</option>
</select></div></td><td>&nbsp;</td><td><input type="text" size="12" name="words" value="" /></td><td>&nbsp;</td><td><input type="submit" name="Search" value="Search" /></td></tr></table></form></td>
		<td align="right">				<b><a style="color: #FFFFFF" href="/account/logout.php">Log Out</a></b><br />
				<b><a style="color: #FFFFFF" href="/account/">My Account</a></b>
				
		<form name="quicknavform">
			<select name="quicknav" onChange="location.href=document.quicknavform.quicknav.value">
				<option value="">Quick Jump To...</option>
				<option value="/projects/cadcoq/">CAD_COQ</option>
				<option value="/project/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/tracker/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Tracker</option>
				<option value="/tracker/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/pm/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Task Manager</option>
				<option value="/pm/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/frs/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Files</option>
				<option value="/frs/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/scm/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SCM</option>
				<option value="/forum/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Forum</option>
				<option value="/forum/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/mail/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Lists</option>
				<option value="/mail/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/docman/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Docs</option>
				<option value="/docman/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/news/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;News</option>
				<option value="/news/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/survey/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Surveys</option>
				<option value="/survey/admin/?group_id=154">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/projects/coqart/">coqart</option>
				<option value="/tracker/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Tracker</option>
				<option value="/tracker/admin/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/pm/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Task Manager</option>
				<option value="/frs/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Files</option>
				<option value="/scm/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SCM</option>
				<option value="/forum/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Forum</option>
				<option value="/mail/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Lists</option>
				<option value="/docman/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Docs</option>
				<option value="/news/?group_id=155">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;News</option>
				<option value="/projects/coqfinitgroup/">CoqFiniteGroups</option>
				<option value="/project/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/tracker/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Tracker</option>
				<option value="/tracker/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/pm/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Task Manager</option>
				<option value="/pm/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/frs/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Files</option>
				<option value="/frs/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/scm/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SCM</option>
				<option value="/forum/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Forum</option>
				<option value="/forum/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/mail/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Lists</option>
				<option value="/mail/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/docman/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Docs</option>
				<option value="/docman/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/news/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;News</option>
				<option value="/news/admin/?group_id=401">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/projects/marelledocs/">marelledocs</option>
				<option value="/tracker/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Tracker</option>
				<option value="/tracker/admin/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Admin</option>
				<option value="/pm/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Task Manager</option>
				<option value="/frs/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Files</option>
				<option value="/scm/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SCM</option>
				<option value="/forum/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Forum</option>
				<option value="/mail/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Lists</option>
				<option value="/docman/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Docs</option>
				<option value="/news/?group_id=148">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;News</option>
				<option value="/projects/wumethod/">WuMethod</option>
				<option value="/scm/?group_id=596">&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SCM</option>
			</select>
		</form></td>
		<td>&nbsp;&nbsp;</td>
	</tr>

</table>

<table border="0" width="100%" cellspacing="0" cellpadding="0">

	<tr>
		<td>&nbsp;</td>
		<td colspan="3">



		<!-- start tabs -->

		<table border="0" cellpadding="0" cellspacing="0" width="100%">
		<tr>
					<td valign="top" width="10" background="/themes/inria/images/theme-toptab-end-notselected.png"><img src="/themes/inria/images/clear.png" height="25" width="10" alt="" /></td><td background="/themes/inria/images/theme-toptab-notselected-bg.png" width="20%" align="center"><a class="tablink" href="/">Home</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-toptab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-toptab-notselected-bg.png" width="20%" align="center"><a class="tablink" href="/my/">My&nbsp;Page</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-toptab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-toptab-notselected-bg.png" width="20%" align="center"><a class="tablink" href="/softwaremap/">Project&nbsp;Tree</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-toptab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-toptab-notselected-bg.png" width="20%" align="center"><a class="tablink" href="/people/">Project&nbsp;Openings</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-toptab-notselected-selected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-toptab-selected-bg.png" width="20%" align="center"><a class="tabsellink" href="/projects/coqfinitgroup/">CoqFiniteGroups</a></td>
					<td valign="top" width="10" background="/themes/inria/images/theme-toptab-selected-end.png"><img src="/themes/inria/images/clear.png" height="2" width="10" alt="" /></td></tr><tr><td colspan="12" height="1" bgcolor="#909090"><img src="/themes/inria/images/clear.png" height="1" width="10" /></td><td colspan="3" height="1" bgcolor="#e0e0e0"><img src="/themes/inria/images/clear.png" height="1" width="10" /></td></tr>
		</table> 

		<!-- end tabs -->

		</td>
		<td>&nbsp;</td>
	</tr>

	<tr>
		<td align="left" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/topleft.png" height="9" width="9" alt="" /></td>
		<td bgcolor="#E0E0E0" width="30"><img src="/themes/inria/images/clear.png" width="30" height="1" alt="" /></td>
		<td bgcolor="#E0E0E0"><img src="/themes/inria/images/clear.png" width="1" height="1" alt="" /></td>
		<td bgcolor="#E0E0E0" width="30"><img src="/themes/inria/images/clear.png" width="30" height="1" alt="" /></td>
		<td align="right" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/topright.png" height="9" width="9" alt="" /></td>
	</tr>

	<tr>

		<!-- Outer body row -->

		<td bgcolor="#E0E0E0"><img src="/themes/inria/images/clear.png" width="10" height="1" alt="" /></td>
		<td valign="top" width="99%" bgcolor="#E0E0E0" colspan="3">

			<!-- Inner Tabs / Shell -->

			<table border="0" width="100%" cellspacing="0" cellpadding="0">
			<tr>
				<td>&nbsp;</td>
				<td>
				

		<!-- start tabs -->

		<table border="0" cellpadding="0" cellspacing="0" width="100%">
		<tr>
					<td valign="top" width="10" background="/themes/inria/images/theme-bottomtab-end-notselected.png"><img src="/themes/inria/images/clear.png" height="25" width="10" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/projects/coqfinitgroup/">Summary</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/project/admin/?group_id=401">Admin</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/forum/?group_id=401">Forums</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/tracker/?group_id=401">Tracker</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/mail/?group_id=401">Lists</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/pm/?group_id=401">Tasks</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/docman/?group_id=401">Docs</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/news/?group_id=401">News</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-selected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-selected-bg.png" width="9%" align="center"><a class="tabsellink" href="/scm/?group_id=401">CVS/SVN</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-selected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/frs/?group_id=401">Files</a></td>
					<td colspan="2" valign="top" width="20" background="/themes/inria/images/theme-bottomtab-notselected-notselected.png"><img src="/themes/inria/images/clear.png" height="2" width="20" alt="" /></td><td background="/themes/inria/images/theme-bottomtab-notselected-bg.png" width="9%" align="center"><a class="tablink" href="/plugins/wiki/index.php?id=401&type=g">Wiki</a></td>
					<td valign="top" width="10" background="/themes/inria/images/theme-bottomtab-notselected-end.png"><img src="/themes/inria/images/clear.png" height="2" width="10" alt="" /></td></tr><tr><td colspan="24" height="1" bgcolor="#909090"><img src="/themes/inria/images/clear.png" height="1" width="10" /></td><td colspan="3" height="1" bgcolor="white"><img src="/themes/inria/images/clear.png" height="1" width="10" /></td><td colspan="6" height="1" bgcolor="#909090"><img src="/themes/inria/images/clear.png" height="1" width="10" /></td></tr>
		</table> 

		<!-- end tabs -->
				</td>
				<td>&nbsp;</td>
			</tr>
						<tr>
				<td align="left" bgcolor="#ffffff" width="9"><img src="/themes/inria/images/tabs/topleft-inner.png" height="9" width="9" alt="" /></td>
				<td bgcolor="#ffffff"><img src="/themes/inria/images/clear.png" width="1" height="1" alt="" /></td>
				<td align="right" bgcolor="#ffffff" width="9"><img src="/themes/inria/images/tabs/topright-inner.png" height="9" width="9" alt="" /></td>
			</tr>

			<tr>
				<td bgcolor="#ffffff"><img src="/themes/inria/images/clear.png" width="10" height="1" alt="" /></td>
				<td valign="top" width="99%" bgcolor="white">

	
			<p><strong>
				<a href="/scm/admin/?group_id=401">Admin</a></strong></p><link href="/plugins/scmsvn/styles.css" rel="stylesheet" TYPE="text/css"><h1>coqfinitgroup: trunk/signperm.v</h1>

<div class="vc_summary">
File: <a href="/plugins/scmsvn/viewcvs.php/?rev=495&root=coqfinitgroup#dirlist">[coqfinitgroup]</a> / <a href="/plugins/scmsvn/viewcvs.php/trunk/?rev=495&root=coqfinitgroup#dirlist">trunk</a> / signperm.v
(<a href="/plugins/scmsvn/viewcvs.php/*checkout*/trunk/signperm.v?rev=495&root=coqfinitgroup"><b>download</b></a>)

<br>

Revision: <b>495</b>,
<i>Wed Aug  8 15:00:23 2007 UTC</i> (7 weeks, 5 days ago) by <i>sbiha</i>





<br>File size: 11221 byte(s)


<pre class="vc_log">packaging indexed_prod</pre>

</div>
<pre>Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp action.

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.

(* We don't use the bool group structure directly here, but we may need it to *)
(* make the parity function is a morphism S_n -&gt; bool, e.g., to define A_n as *)
(* its kernel.                                                                *)
Canonical Structure boolGroup :=
  @FinGroupType _ _ (fun b =&gt; b) addb addFb addbb addbA.

(* Porting the eqType / finType structure of eq_pair to pairs *)
(* To be complete we should also port the group structure, to *)
(* get the direct product.                                    *)

Section PermutationComplements.

Variable d : finType.

(* This should really be in group_perm *)

(* This is a crutch: if permutations coerced to fgraphs, this *)
(* wouln't be needed.                                         *)
Lemma p2f : forall f Uf, @Perm d (EqSig _ (fgraph_of_fun f) Uf) =1 f.
Proof. move=&gt; *; exact: g2f. Qed.

Lemma perm1 : forall x, (1 : permType d) x = x.
Proof. by move=&gt; x; rewrite p2f. Qed.

Lemma permM : forall (s1 s2 : permType d) x, (s1 * s2) x = s2 (s1 x).
Proof. by move=&gt; *; rewrite p2f. Qed.

Lemma permK : forall s : permType d, cancel s s^-1.
Proof. by move=&gt; s x; rewrite -permM mulgV perm1. Qed. 

Lemma permKv : forall s : permType d, cancel s^-1 s.
Proof. by move=&gt; s; have:= permK s^-1; rewrite invgK. Qed.

Lemma permJ : forall (s t: permType d) x, (s ^ t) (t x) = t (s x).
Proof. by move=&gt; *; rewrite !permM permK. Qed.

End PermutationComplements.

(* Shorten the name for tranpositions, to improve usability *)

Notation transp := (@transperm _).

Section PermutationParity.

Variable d : finType.

(* Lifting permutations to pairs, with local shorthand. *)

Definition perm_pair (s : permType d) p :=
  let: (x, y) := p in (s x, s y).
Notation Local permp := perm_pair.

Lemma perm_pair1 : forall p, permp 1 p = p. 
Proof. by move=&gt; [x y] /=; rewrite !perm1. Qed.
Notation Local permp1 := perm_pair1.
 
Lemma perm_pairM : forall s t p, permp (s * t) p = permp t (permp s p).
Proof. by move=&gt; s t [x y] /=; rewrite !permM. Qed.
Notation Local permpM := perm_pairM.

Lemma perm_pairK : forall s, cancel (permp s) (permp s^-1).
Proof. by move=&gt; s p; rewrite -permpM mulgV permp1. Qed.
Notation Local permpK := perm_pairK.

Definition perm_pair_inj s := can_inj (permpK s).
Notation Local permpI := (@perm_pair_inj).
Hint Resolve perm_pair_inj.

Lemma image_perm_pair : 
  forall s A p, image (permp s) A p = A (permp s^-1 p).
Proof. by move=&gt; s A p; rewrite -{1}(permpK s^-1 p) invgK (image_f _ (permpI s)). Qed.

Notation Local im_permp := image_perm_pair.

(* Flipping components of a pair *)

Definition flip_pair A p : A * A := let: (x, y) := p in (y, x).
Notation Local flip := (@flip_pair d).

Lemma flip_pairK : involutive flip.
Proof. by case. Qed.
Notation Local flipK := flip_pairK.

Definition flip_pair_inj := inv_inj flipK.
Notation Local flipI := flip_pair_inj.

Lemma image_flip_pair : forall p A, image flip A p = A (flip p).
Proof. by move=&gt; p A; rewrite -{1}(flipK p) (image_f _ flipI). Qed.
Notation Local im_flip := image_flip_pair.

Lemma perm_flip_pair : forall s p, permp s (flip p) = flip (permp s p).
Proof. by move=&gt; s [x y]. Qed.
Notation Local permp_flip := perm_flip_pair.

(* Inversions are defined abstractly in terms of an "ordered_pair" relation. *)
(* The only required properties for that relation are antisymmetry and       *)
(* antirelexivity, which are conveniently expressed in terms of the "flip"   *)
(* operation. The actual definition compares indices, but we don't use the   *)
(* transitivity, except in an alternate proof that transpositions are odd.   *)

Definition ordered_pair p := index (fst p) (enum d) &lt; index (snd p) (enum d).
Notation Local opair := ordered_pair.

Lemma ordered_pair_flip : forall p, opair (flip p) = (flip p != p) &amp;&amp; ~~ opair p.
Proof.
case=&gt; x y /=; rewrite /opair ltn_neqAle -leqNgt; congr andb; congr negb.
rewrite {2}/set1 /= /pair_eq /= (eq_sym y) andbb; apply/eqP/eqP=&gt; [|-&gt; //].
by rewrite -{2}(sub_index x (mem_enum y)) =&gt; -&gt;; rewrite sub_index // mem_enum.
Qed.
Notation Local opair_flip := ordered_pair_flip.

Definition inversion s p := opair (flip (permp s p)).
Notation Local invn := inversion.

Definition odd_perm s := odd (card (setI opair (inversion s))).
Definition even_perm s := ~~ odd_perm s.
Notation Local oddp := odd_perm.

Lemma odd_permM : forall s t, oddp (s * t) = oddp s (+) oddp t.
Proof.
move=&gt; s t; rewrite /oddp -(cardIC (inversion s)); symmetry.
rewrite -(cardIC (inversion (s * t))) addbC -(card_image (permpI s^-1)) -(cardIC opair).
rewrite !odd_addn addbCA !addbA -addbA addbC -addbA; set n1 := card _; set n2 := card _.
suffices -&gt; : n2 = n1.
  rewrite addbK /setI /setC; congr 2 (odd _ (+) odd _); apply: eq_card=&gt; p /=.
    by rewrite andbC andbCA andbA.
  rewrite im_permp invgK /inversion -permpM !opair_flip -!permp_flip !(inj_eq (permpI _)).
  by case: (_ != p); rewrite ?andbF //= negbK -andbA andbC -!andbA andbCA.
rewrite /n2 -(card_image flipI); apply: eq_card =&gt; p /=.
rewrite /setI /setC im_flip im_permp invgK /inversion !permp_flip !flipK -permpM.
by rewrite !opair_flip -permp_flip (inj_eq (@permpI _)) -!andbA; do !bool_congr.
Qed.
Notation Local oddpM := odd_permM.

Lemma odd_perm1 : oddp 1 = false.
Proof. by rewrite -[1]mulg1 oddpM addbb. Qed.
Notation Local oddp1 := odd_perm1.

Lemma odd_permV : forall s, oddp s^-1 = oddp s.
Proof. by move=&gt; s; rewrite -{2}(mulgK s s) !oddpM addbb. Qed.
Notation Local oddpV := odd_permV.

Lemma odd_permJ : forall s t, oddp (s ^ t) = oddp s.
Proof. by move=&gt; *; rewrite /conjg !oddpM oddpV addbC addbA addbb. Qed.
Notation Local oddpJ := odd_permJ.

(* Complements on tranpositions, starting with a shorter prenex alias. *)

CoInductive transp_spec (x y z : d) : d -&gt; Type :=
  | TranspFirst of z = x          : transp_spec x y z y
  | TranspSecond of z = y         : transp_spec x y z x
  | TranspNone of z &lt;&gt; x &amp; z &lt;&gt; y : transp_spec x y z z.

Lemma transpP : forall x y z, transp_spec x y z (transp x y z).
Proof. by move=&gt; x y z; rewrite p2f /transpose; do 2?[case: eqP =&gt; /=]; constructor; auto. Qed.

Lemma transpL : forall x y : d, transp x y x = y.
Proof. by move=&gt; x y; case transpP. Qed.

Lemma transpR : forall x y : d, transp x y y = x.
Proof. by move=&gt; x y; case transpP. Qed.

Lemma transpC : forall x y : d, transp x y = transp y x.
Proof. by move=&gt; *; apply: eq_fun_of_perm =&gt; ?; do 2![case: transpP =&gt; //] =&gt; -&gt;. Qed.

Lemma transp1 : forall x : d, transp x x = 1.
Proof. by move=&gt; *; apply: eq_fun_of_perm =&gt; ?; rewrite perm1; case: transpP. Qed.

Lemma transpK : forall x y : d, involutive (transp x y).
Proof. by move=&gt; x y z; do 2![case transpP =&gt; //] =&gt; -&gt;. Qed.

Lemma transpV : forall x y : d, (transp x y)^-1 = transp x y.
Proof.
by move=&gt; x y; apply: eq_fun_of_perm =&gt; z; rewrite -{1}(transpK x y z) permK.
Qed.

Lemma transp2 : forall x y : d, transp x y * transp x y = 1.
Proof. by move=&gt; x y; rewrite -{1}transpV mulVg. Qed.

Lemma inj_transp : forall (d' : finType) (f : d -&gt; d') x y z,
  injective f -&gt; f (transp x y z) = transp (f x) (f y) (f z).
Proof. by move=&gt; d' f x y z injf; rewrite !p2f /transpose !(inj_eq injf) !(fun_if f). Qed.

Lemma transpJ : forall x y (s : permType d), (transp x y)^s = transp (s x) (s y).
Proof.
move=&gt; x y s; apply: eq_fun_of_perm =&gt; z; rewrite -(permKv s z) permJ.
apply: inj_transp; exact: perm_inj.
Qed.

Lemma odd_transp : forall x y, oddp (transp x y) = (x != y).
Proof.
move=&gt; x y; case Dxy: (x == y); first by rewrite (eqP Dxy) transp1 oddp1.
without loss Oxy: x y Dxy / opair (x, y).
  case Oxy: (opair (x, y)); last rewrite transpC; apply=&gt; //; first by rewrite eq_sym.
  by rewrite (opair_flip (x, y)) Oxy andbT; apply/nandP; right; rewrite Dxy.
pose A z p := let: (x', y') := p : d * d in set2 x' y' z.
pose B z p := opair p &amp;&amp; inversion (transp x y) p &amp;&amp; A z p.
have:= congr1 odd (cardUI (B x) (B y)); rewrite !odd_addn.
have-&gt;: card (B x) = card (B y); last rewrite addbb.
  rewrite -(card_image (permpI (transp x y))) -(card_image flipI).
  apply: eq_card =&gt; p; rewrite /= /setI im_flip im_permp transpV.
  rewrite /B /inversion !permp_flip flipK -permpM transp2 permp1 -!andbA; do !bool_congr.
  by case: p =&gt; x' y'; rewrite /A /= /set2 !(inv_eq (transpK _ _)) orbC transpL.
move/(fun H =&gt; canRL H (addKb _)) =&gt; /=.
have-&gt;: odd (card (setU (B x) (B y))) = oddp (transp x y); last move-&gt;.
  congr odd; apply: eq_card=&gt; p /=; rewrite /setI /setU /B.
  case: (@andP (opair p)) =&gt; //=; case; rewrite /inversion opair_flip =&gt; Op; case/andP=&gt; _ Otp.
  apply/norP; case; rewrite /A; case: p =&gt; [x' y'] /= in Op Otp *.
  do 2![case/norP; do 2!move/eqP=&gt; ?]; case/negP: Otp; do 2![case transpP =&gt; //].
rewrite -[true]/(odd 1) -(card1 (x, y)); congr odd.
apply: eq_card =&gt; [[x' y']]; rewrite /setI {}/B {}/A /inversion /= /set1 /= /pair_eq /=.
rewrite /set2 !(eq_sym x) !(eq_sym y); case: eqP =&gt; [-&gt; | _] /=.
  by rewrite Dxy; case: eqP =&gt; [-&gt;|_]; [rewrite transpL transpR Oxy | rewrite !andbF].
apply/and3P; case; case/andP=&gt; _; move/eqP=&gt; -&gt; Oxx'; rewrite Dxy orbF; move/eqP=&gt; Dx'.
by rewrite Dx' -(flipK (y, x)) opair_flip /= Oxy andbF in Oxx'.
Qed.

(* An alternate proof, based on reduction by conjugation.
   It's less abstract, since it depends on the way pairs are ordered.
Lemma signature_transp' : forall x y, oddp (transp x y) = (x != y).
Proof.
move=&gt; x y; have x0 := x; pose z i := sub x0 (enum d) i; pose n := size (enum d).
wlog -&gt;: x y / x = z 0.
  pose p := transp x (z 0); rewrite -(inj_eq (@perm_inj _ p)) -(oddpJ _ p) transpJ.
  apply; exact: transpL.
case Dy0: (z 0 == y) {x} =&gt; /=.
  rewrite -oddp1; congr oddp; apply: eq_fun_of_perm =&gt; x.
  by rewrite (eqP Dy0) perm1; case transpP.
have Ez: forall i, i &lt; n -&gt; index (z i) (enum d) = i.
  move=&gt; i ltid; exact: index_uniq ltid (uniq_enum d).
have Iz: exists2 i, i &lt; n &amp; z i = _ by move=&gt; t; apply/subP; exact: mem_enum.
have eqz: forall i j, i &lt; n -&gt; j &lt; n -&gt; (z i == z j) = (i == j).
  move=&gt; i j; move/Ez=&gt; Di; move/Ez=&gt; Dj.
  by apply/eqP/eqP=&gt; [Dzi | -&gt; //]; rewrite -Di Dzi Dj.
have lt1n: 1 &lt; n; last have lt0n := ltnW lt1n.
  case: (Iz y) =&gt; [i ltin Dy]; rewrite -{}Dy in Dy0.
  by apply: leq_trans ltin; case: i Dy0 =&gt; //; rewrite set11.
wlog{Dy0} -&gt;: y / y = z 1%nat.
  rewrite -(oddpJ _ (transp y (z 1%nat))) transpJ =&gt; Wy.
  case: transpP; by [move/eqP; rewrite ?Dy0 ?eqz | rewrite transpL Wy].
rewrite -[true]/(odd 1) -{2}(card1 (z 0, z 1%nat)) {y}; congr odd.
apply: eq_card=&gt; [[u1 u2]]; case: (Iz u1) (Iz u2) =&gt; [i1 i1P &lt;-] [i2 i2P &lt;-] {u1 u2}.
do 2!rewrite /set1 /=; rewrite /setI /inversion /opair /= !Ez //.
rewrite /fun_of_perm !g2f /transpose -!(fun_if z) !eqz //.
case: i2 i1 =&gt; [|[|i2]] [|[|i1]] //= in i1P i2P *; rewrite !Ez //= !ltnS.
by apply/andP; case=&gt; lti12; rewrite ltnNge ltnW.
Qed.
*)

End PermutationParity.

Coercion odd_perm : permType &gt;-&gt; bool.
</pre>

<hr noshade>
<table width="100%" border="0" cellpadding="0" cellspacing="0">
<tr>
<td align="left">
<address><a href="mailto:webmaster@gforge.inria.fr">CVS/SVN Admin</a></address><br />
Powered by <a href="http://viewcvs.sourceforge.net/">ViewCVS 1.0-dev</a>
</td>
<td align="right">
<img src="/doc/viewcvs/images/logo.png" alt="(Powered by ViewCVS)" border="0"
width="128" height="48" /><br />
<h3><a target="_blank" href="/plugins/scmsvn/viewcvs/help_rootview.html">ViewCVS and CVS/SVN Help</a></h3>
</td>
</tr>
</table>
<!--
</body>
</html>
-->
			&nbsp;<p>
		<center>
		In case of problems, mail the <a href="mailto:help.et.gforge_AT_inria.fr">administrators</a> or file a <a href="http://gforge.inria.fr/tracker/?func=browse&group_id=1&atid=110">bug</a>.
		</center>

			<!-- end main body row -->



				</td>
				<td width="10" bgcolor="#ffffff"><img src="/themes/inria/images/clear.png" width="2" height="1" alt="" /></td>
			</tr>
			<tr>
				<td align="left" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/bottomleft-inner.png" height="11" width="11" alt="" /></td>
				<td bgcolor="#ffffff"><img src="/themes/inria/images/clear.png" width="1" height="1" alt="" /></td>
				<td align="right" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/bottomright-inner.png" height="11" width="11" alt="" /></td>
			</tr>
			</table>

		<!-- end inner body row -->

		</td>
		<td width="10" bgcolor="#E0E0E0"><img src="/themes/inria/images/clear.png" width="2" height="1" alt="" /></td>
	</tr>
	<tr>
		<td align="left" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/bottomleft.png" height="9" width="9" alt="" /></td>
		<td bgcolor="#E0E0E0" colspan="3"><img src="/themes/inria/images/clear.png" width="1" height="1" alt="" /></td>
		<td align="right" bgcolor="#E0E0E0" width="9"><img src="/themes/inria/images/tabs/bottomright.png" height="9" width="9" alt="" /></td>
	</tr>
</table>

<!-- PLEASE LEAVE "Powered By GForge" on your site -->
<br />
<center>
<a href="http://gforge.org/"><img src="/images/pow-gforge.png" alt="Powered By GForge Collaborative Development Environment" border="0" /></a>
</center>


</body>
</html>
