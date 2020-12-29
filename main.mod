# IEMS-313.
#
# main.mod.
#
# Reference document:
#
# https://www.overleaf.com/read/hxkpxgrkndcq

#######################################################################################

#
# Usage at the AMPL terminal:
#
#   # First makes sure you have both main.mod AND constants.dat in the same directory.
#   # This directory to be exact!
#   reset;
#   model main.mod;
#   data _____________________.dat;    # example_1.dat works if you want to look.
#   solve;
#
# # Then look at any variables you find interesting.
#

#######################################################################################

# Most of the sets in this project do not actually change all that much from schedule
# to schedule. However, in the course of coding this up, we came to find that AMPL is
# actually singularly awful at the model/data divide it artificially imposes on the
# programmer. In particular, the `x .. y by z` construct does not work in the .dat
# files, but if you define sets in the .mod files, then you lose the ability to wrap
# them up into sets-of-sets later on, which is key for our project. The best compromise
# we could come up with was to stick to purely logic-based programming here, while
# hiding the fact that almost all of these sets have to be hardcoded in a separate
# .dat file, which we called "unchanging-sets.dat".

# Set C of calendar days.
set C;

# Sets M_i of calendar months.
set numMonths := 1 .. 12;
set M_i {numMonths} within C;

# Sets D_i of 4-day rolling periods.
set numRolling := 1 .. 362;
set D_i {numRolling} within C;

# Set C_hol of holidays.
set C_hol within C;

# Set C_wk of weekends.
set C_wk within C;

# Set C_Fri of Fridays.
set C_Fri within C;


# Sets of days second- and third-year residents are allowed to work.
# Not  strictly needed within the reference document; we put them here
# because they make later code easier.
set C_R_2 within C;
set C_R_3 within C;


# Set of hospital shifts.
set H;

# Set of hospital shifts h \in H that can be staffed by the EOC. A technicality
# enforced by the problem.
set H_EOC within H;

# Set of days hospital shift h \in H that need staffing.
set C_h {H} within C;


# These two lines  pull the data we need for the above variables out of
# constants.dat, where they are hardcoded, and then return us to model mode.
data constants.dat;
model;

#######################################################################################

# Code to implement C_r, C_hr, and V_r, from the reference documents.

# Set of residents and EOC; set of residents; set of 2nd and 3rd year residents.
set R_star;
set R within R_star;
set R_2 within R;
set R_3 within R;

# Set of days resident, or EOC, r \in R_star is allowed to work.
# AMPL's conditional formatting leaves something to be desired, but basically,
# this says if a resident is second-year, give them the second-year schedule from
# unchanging-sets; if they're third-year, give them the third-year schedule; if
# they're in R_star but not R, then they're an EOC, so let them work the whole
# year; and if they're somehow in R without being in R_2 or R_3, then something
# weird and erroneous happened, so throw up an error.
set C_r {r in R_star} :=
	if (r in R_2) then C_R_2 
	else
		(if (r in R_3) then C_R_3 
		else
			(if r in (R_star diff R) then C
				else
				{}));

# Set of days hospital shift h \in H can be covered by resident or EOC r \in R_star.
# Strictly speaking in the document, it's defined with r \in R, but this makes the
# code easier to reason about.
set C_hr {h in H,r in R_star} within C := C_h[h] inter C_r[r];

# Set of vacation days, raw.
set V_r_raw {r in R} within C;

# Set of vacation days, cleaned up.
set V_r {r in R} within C := (V_r_raw[r] inter C_r[r]);


#######################################################################################

# Okay. That's all of the sets and indices we need, properly defined. Now we can
# get to the real work - implementing the program itself.

# We move on to defining our decision variables. Note that our non-negativity
# constraints are all baked in here, instead of being listed as constraints later
# in their own right - one of few ways AMPL saves time.

# Number of hours scheduled to resident or EOC r \in R_star, at hospital shift h \in H,
# on calendar day c \in C.
var x_rhc {r in R_star, h in H, c in C} >= 0;

# Binary variable used to indicate whether or not resident or EOC r \in R_star
# is taking hospital shift h \in H on calendar day c \in C.
var y_rhc {r in R_star, h in H, c in C} binary;


# Hours worked by resident r, beyond minimum residency requirements.
var e_r_tot_plus {r in R} >= 0;

# Highest number of overtime hours worked by any resident.
var e_max_tot_plus >= 0;


# Hours worked by resident r on the weekends, beyond 30 pc. of their total.
var e_r_wk_plus {r in R} >= 0;

# Highest number of weekend overtime hours worked by any resident.
var e_max_wk_plus >= 0;


# Hours worked by resident r on Fridays, beyond 15 pc. of their total
var e_r_Fri_plus {r in R} >= 0;

# Highest number of Friday overtime hours worked by any resident.
var e_max_Fri_plus >= 0;


# And here's the related v_r data.
param v_r {r in R} :=
	if
	  (card(V_r[r]) > 0)
	then
	  (15 * card(V_r[r]))
	else
       0;

# Number of vacation hours given off to resident r.
var e_r_vac_minus {r in R} >= 0;

# Lowest number of vacation given off to any resident.
var e_min_vac_minus >= 0;

# Number of first-week vacation hours given to resident r.
# Used for a piecewise weighting in the objective function.
var e_r_vac_wk1 {r in R} >= 0;
# Total sum of first-week vacation hours given.
var e_vac_wk1 >= 0;

# Number of second-week vacation hours given to resident r.
# Used for a piecewise weighting in the objective function.
var e_r_vac_wk2 {r in R} >= 0;
# Total sum of second-week vacation hours given.
var e_vac_wk2 >= 0;

# Number of post-second-week vacation hours given to resident r.
# Used for a piecewise weighting in the objective function.
var e_r_vac_wk3 {r in R} >= 0;
# Total sum of post-second-week vacation hours given.
var e_vac_wk3 >= 0;


# Holiday hours worked by resident r, above ideal.
var e_r_hol_plus {r in R} >= 0;
# Holiday hours worked by resident r, below ideal.
var e_r_hol_minus {r in R} >= 0;

# Highest number of holiday hours above ideal assigned to any resident.
var e_max_hol_plus >= 0;
# Highest number of holiday hours below ideal assigned to any resident.
var e_max_hol_minus >= 0;


# Dashboard variable t_r, a total of the amount of hours each resident / EOC is
# slated for.
var t_r {r in R_star} >= 0;

# Dashboard variable t_r_wk, a total of the amount of hours each resident is
# slated for on the weekends.
var t_r_wk {r in R} >= 0;

# Dashboard variable t_r_Fri, a total of the amount of hours each resident is
# slated for on Fridays.
var t_r_Fri {r in R} >= 0;

# Dashboard variable t_r_vac, a total of the amount of hours each resident is
# slated for on their vacation days.
var t_r_vac {r in R} >= 0;

# Dashboard variable t_r_hol, a total of the amount of hours each resident is
# slated for on their vacation days.
var t_r_hol {r in R} >= 0;

# Dashboard variable C_EOCs, a total of the cost of all EOCs hired on this schedule.
var C_EOCs >= 0;
    

#######################################################################################

# Parameter guide 

# These are the 5 parameters that are used in the weighting of the objective function.
# You need to define these in a separate file called something like "params.dat",
# and then load that data in before you try to `solve;` anything here.
#
# If you set any of these to 0, it effectively **removes** that constraint from being
# considered in the first place. So, for example, if all you care about is reducing
# total overtime hours, set c1 to be 1 and the rest to be 0. What kind of calendar
# would you expect from that kind of model? One whose optimal solution would have it
# so that every second-year resident has exactly the same number of total hours as
# any other second-year resident, and any third-year resident has exactly the same
# number of total hours as any third-year resident.

# Make this higher to reduce the highest number of total hours over minimum residency
# requirements any resident r is assigned.
param c_1; 

# Make this higher to reduce the highest number of total weekend hours over residential
# preference any resident r is assigned.
param c_2;

# Make this higher to reduce the highest number of total Friday hours over residential
# preference any resident r is assigned.
param c_3;

# Make this higher to increase the number of total vacation hours any resident
# r is given off.
param c_4;

# Make this higher to reduce the number of holiday hours above or below what is desired
# any resident r is assigned.
param c_5;

# Make this higher to make the average amount of vacation hours every resident gets
# closer together.
param c_6;

# Make this higher to cause the EOC to be scheduled in for fewer hours.
param c_7;

#######################################################################################

# Objective function and constraints.

# Objective: Minimize all of these terms as weighted by their preferences.
minimize f:
	+ c_1 * e_max_tot_plus
	+ c_2 * e_max_wk_plus
	+ c_3 * e_max_Fri_plus
	- c_4 * e_min_vac_minus
	+ c_5 * (e_max_hol_plus + e_max_hol_minus)
	- c_6 * ( 0.5 * e_vac_wk1 + 
	          0.25 * e_vac_wk2 +
	          0.125 * e_vac_wk3    )
	+ c_7 * C_EOCs;

#######################################################################################

# Hard constraints.
# These are constraints that *must* be satisfied. No slack variables allowed.
# Failing to satisfy all of these will result in an infeasible solution.

# Non-negativity constraints are baked in to how we defined the decision variables in
# the first place, so no need to repeat them here.

subject to

  # EOC stays at Cooper only: The EOC is only allowed to work shifts
  # at Cooper, not either of Baker's shifts.
  eoc_cooper_only {r in R_star diff R, h in H diff H_EOC, c in C}:
    x_rhc[r,h,c] = 0;

  # No clones: A resident or EOC r \in R_star can only work up to 
  # 15 hours across all hospital shifts in one night.
  no_clones {r in R_star, c in C}:
    sum {h in H} x_rhc[r,h,c] <= 15;

  # Full staffing: Every hospital shift h needs every day in C_h fully covered.
  # No more, no less.
  full_staffing {h in H, c in C_h[h]}:
    sum {r in R_star} x_rhc[r,h,c] = 15;
  
  # No off-day scheduling: A resident can't be scheduled to any day they cannot
  # work, or any day a given hospital shift isn't open.
  no_off_days {r in R, h in H, c in (C diff C_hr[h,r])}:
    x_rhc[r,h,c] = 0;
  
  # Monthly limit: No resident may work more than 75 hours in any calendar month.
  monthly_limit {r in R, i in numMonths}:
    sum {c in M_i[i]} (sum {h in H} x_rhc[r,h,c]) <= 75;
  
  # 4-day limit: No resident may work more than 15 hours in any 4-day period.
  4_day_limit {r in R, i in numRolling}:
    sum {c in D_i[i]} (sum {h in H} x_rhc[r,h,c]) <= 15;
    
  # On-call whole shift: In Project 2, if someone is on call for one hospital
  # shift, they are on for the *entire* shift.
  on_call_whole_shift {r in R_star, h in H, c in C}:
    x_rhc[r,h,c] = 15 * y_rhc[r,h,c];

#######################################################################################

# Soft constraints.
# These are constraints where we start to add in the e_whatever terms.

subject to
  # EOC can only work at Cooper.
  # Minimum residency: Second-year residents need to work at minimum 600 hours,
  # third-years 720. Anything above that is extra and gets tossed into their 
  # e_r_tot_plus term to get minimized later on.
  year_2_min_res {r in R_2}:
    (sum {c in C} (sum {h in H} x_rhc[r,h,c])) - e_r_tot_plus[r] = 600;
  year_3_min_res {r in R_3}:
    (sum {c in C} (sum {h in H} x_rhc[r,h,c])) - e_r_tot_plus[r] = 720;
  # Highest error term: This constraint ensures that e_max_tot_plus captures
  # the highest total overtime any resident is scheduled for.
  highest_error_term_min_res {r in R}:
    e_max_tot_plus >= e_r_tot_plus[r];
  
  # Weekend preferences: Residents prefer not to have more than 30% of their 
  # hours on the weekend. Anything above that goes into their e_r_wk_plus
  # term to get minimized later on.
  #
  # Change from Project 1: We changed this to a <= expression, in order to 
  # avoid infeasibility if the system gives fewer than p_wk percent
  # weekend hours. Thanks, TA Xinyi!
  weekend_prefs {r in R}:
  	(sum {c in C_wk} (sum {h in H} x_rhc[r,h,c])) - e_r_wk_plus[r]
  	<= 0.3 * (sum {c in C} (sum {h in H} x_rhc[r,h,c]));
  # Highest error term: This constraint ensures that e_max_wk_plus captures
  # the highest total weekend overtime any resident is scheduled for.
  highest_error_term_weekend_prefs {r in R}:
    e_max_wk_plus >= e_r_wk_plus[r];
    
  # Friday preferences: Residents prefer not to be scheduled for Friday, either. 
  # We decided to weight it so that residents prefer not to have have more than 
  # 15% of their Friday hours scheduled. Anything above that goesinto their
  # e_r_Fri_plus term.
  #
  # Change from Project 1: We changed this to a <= expression, in order to 
  # avoid infeasibility if the system gives fewer than p_Fri percent
  # Friday hours. Thanks, TA Xinyi!
  friday_prefs {r in R}:
  	(sum {c in C_Fri} (sum {h in H} x_rhc[r,h,c])) - e_r_Fri_plus[r]
  	<= 0.15 * (sum {c in C} (sum {h in H} x_rhc[r,h,c]));
  # Highest error term: This constraint ensures that e_max_Fri_plus captures
  # the highest total Friday overtime any resident is scheduled for.
  highest_error_term_friday_prefs {r in R}:
    e_max_Fri_plus >= e_r_Fri_plus[r];
    
  # Vacation sanity: You can't give a resident more vacation hours than they
  # actually asked for.
  vacation_sanity {r in R}:
  	e_r_vac_minus[r] <= v_r[r];
    
  # Vacation preferences: Residents prefer not to have their vacation hours denied.
  # We use e_r_vac_minus to tally up however many howers we give them off.
  #
  # One of the limitations of the purely linear program is that we cannot use binary
  # variables. We have to represent vacation days as fractional hours of the day. We
  # thought about using a piecewise linear function here to add some further dynamism
  # to the weighting, but decided against it, as this thing is already pretty
  # complicated.
  vacation_prefs {r in R}:
  	  (sum {c in V_r[r]} (15 - (sum {h in H} x_rhc[r,h,c]))) = e_r_vac_minus[r];
  	
  # Lowest error term: This constraint ensures e_min_vac_minus captures the highest
  # amount of total vacation hours any resident is scheduled to.
  highest_error_term_vacation_prefs {r in R}:
      e_min_vac_minus <= e_r_vac_minus[r];
      
  # Vacation piecewise: We're using these variables to implement a piecewise linear
  # function that the objective function kinda-sorta wants to maximize the value of.
  # To do that, however, we need to cap off e_r_vac_wk1 and e_r_vac_wk2 at 7*15=90
  # hours, since they are meant to only measure up to the first vacation weeks' worth
  # of hours given to a resident, and the second vacation weeks' worth, respectively.
  # No such cap is needed for e_r_vac_wk3, since it's meant for all hours the system
  # gives *beyond* two weeks' vacation.
  cap_first_vacation_week {r in R}:
  	e_r_vac_wk1[r] <= 90;
  cap_second_vacation_week {r in R}:
  	e_r_vac_wk2[r] <= 90;
  	
  # Vacation individual summation: We need to sum these terms up per resident, first.
  first_vacation_individual_sum {r in R}:
    e_r_vac_wk1[r] <= e_r_vac_minus[r];
  second_vacation_individual_sum {r in R}:
    e_r_vac_wk2[r] <= e_r_vac_minus[r] - e_r_vac_wk1[r];
  post_second_vacation_individual_sum {r in R}:
    e_r_vac_wk3[r] <= e_r_vac_minus[r] - e_r_vac_wk1[r] - e_r_vac_wk2[r];
  	
  # Vacation summation: We need to sum these terms up in order for them to have the 
  # correct overall effect on the objective function.
  first_vacation_sum:
  	e_vac_wk1 = sum {r in R} e_r_vac_wk1[r];
  second_vacation_sum:
  	e_vac_wk2 = sum {r in R} e_r_vac_wk2[r];
  post_second_vacation_sum:
  	e_vac_wk3 = sum {r in R} e_r_vac_wk3[r];
    
    
  # Holiday hour preferences: Residents prefer to have as close to 15 holiday hours
  # scheduled for the year as possible. We use e_r_hol_plus and e_r_hol_minus to tally
  # up how much we over- or under-shoot that amount, respectively.
  holiday_prefs {r in R}:
    (sum {c in C_hol} (sum {h in H} x_rhc[r,h,c])) - (e_r_hol_plus[r] - e_r_hol_minus[r]) = 15;
    
  # Highest error term: These constraints ensure e_max_hol_plus and e_max_hol_minus
  # respectively capture the highest amount of over- and under-shoot of holiday hours
  # amount for any resident, respectively.
  highest_error_term_holiday_prefs_plus {r in R}:
    e_max_hol_plus >= e_r_hol_plus[r];
  highest_error_term_holiday_prefs_minus {r in R}:
    e_max_hol_plus >= e_r_hol_minus[r];
    
#######################################################################################

# Dashboard variables.

# These are technically decision variables, but they don't actually affect the core of
# the program in any way, so we don't really worry aobut them too much except as an
# afterthought. They do make reporting on the code quite easy, though.

subject to
  # t_r : Counts up the total number of hours each resident and EOC is on call for.
  dashboard_t_r {r in R_star}:
    t_r[r] = sum {h in H} (sum {c in C} x_rhc[r,h,c]);
    
  # t_r_wk : Counts up the total number of weekend hours each resident is on call for.
  dashboard_t_r_wk {r in R}:
    t_r_wk[r] = sum {h in H} (sum {c in C_wk} x_rhc[r,h,c]);
  
  # t_r_Fri: Counts up the total number of Friday hours each resident is on call for.
  dashboard_t_r_Fri {r in R}:
  	t_r_Fri[r] = sum {h in H} (sum {c in C_Fri} x_rhc[r,h,c]);
  
  # t_r_vac: Counts up the total number of vacation hours each resident is on call for.
  dashboard_t_r_vac {r in R}:
  	t_r_vac[r] = (sum {h in H} (sum {c in V_r[r]} x_rhc[r,h,c]));
  
  # t_r_hol: Counts up the total number of holiday hours each resident is on call for.
  dashboard_t_r_hol {r in R}:
  	t_r_hol[r] = sum {h in H} (sum {c in C_hol} x_rhc[r,h,c]);
  
  # C_EOCs: Counts up the total cost of hiring EOCs on this schedule.
  dashboard_C_EOCs:
  	C_EOCs = 80 * (sum  {r in R_star diff R}
  	                 (sum {h in H}
  	                   (sum {c in C} x_rhc[r,h,c])));
  	
  	    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
