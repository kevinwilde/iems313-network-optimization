# This is the header for an AMPL model for the class project (phase 2)
# IEMS 313
#
# Paige Janac, Charles Novek, Kevin Wilde

###################################################
#  STATIONS

# Set of nodes (stations) in the network
set STATIONS;

# Coordinates of nodes in miles
param x_coor{STATIONS};
param y_coor{STATIONS};

# Compute the distance between each pair of nodes
param distance{i in STATIONS, j in STATIONS} :=
   sqrt((x_coor[i]-x_coor[j])^2 + (y_coor[i]-y_coor[j])^2);

# Maximum number of units of incoming goods (including what comes from a
# source) that one reloading building can handle 
param load_per_building;

# Number of reloading buildings already available at each station
param reload_bldg_exist{STATIONS};

# cost for building additional reloading building (in $1000)
param cost_reload_bldg;

###################################################
#   TRACKS and LINES

# Maximum length of a line
param max_line_length;

# Set with all pairs of stations that are within permissible distance.
# These are directed arcs: for each directed arc we can specify how much 
# goods are transported from station i to station j.
set ARCS := {i in STATIONS, j in STATIONS:
             i != j && distance[i,j] <= max_line_length};

# Set of all possible lines (undirected edges)
set LINES := {(i,j) in ARCS: i < j};

# Maximum number of units of good that can be transported on one track
param track_capacity;

# Number of existing tracks per line
param tracks_exist{LINES} integer, >= 0, default 0;

# 1 if line exists, 0 otherwise
param line_exist{LINES} binary, default 0;

###################################################
#    Deliveries

# Source/Destination pairs for deliveries
set DELIVS within {STATIONS, STATIONS};

# Volume of goods shipped from source to destination for each delivery
# (in units of goods)
param volume{DELIVS};

# cost for building a new line from scratch ($1000/mile)
param cost_new_line;

# cost for adding additional track to existing line ($1000/mile)
param cost_add_track;

# Big M used to make sure x_num_tracks[i,j] > 0 if and only if
# x_line_exist[i,j] = 1
param M := (1/track_capacity) * sum{(s,d) in DELIVS} volume[s,d];


###################################################
# VARIABLES

# Number of reloading buildings at each station
var x_num_reload_bldg{STATIONS} >= 0, integer;

# Number of tracks from station i to station j
var x_num_tracks{ARCS} >= 0, integer;

# 1 if line exists from station i to station j, 0 otherwise
var x_line_exist{LINES} binary;

# Number of units in delivery m that are shipped along track
# from station i to station j
var x_num_units{(s,d) in DELIVS, (i,j) in ARCS} >= 0, integer;


###################################################
# OBJECTIVE

# Minimize total cost
minimize total_cost:
  cost_reload_bldg * sum{i in STATIONS} x_num_reload_bldg[i]   				# Cost of reloading buildings at each station
  - cost_reload_bldg * sum{i in STATIONS} reload_bldg_exist[i] 				# Take away cost of existing buildings
  + cost_add_track * sum{(i,j) in ARCS} distance[i,j]*x_num_tracks[i,j]     # Cost of track
  - cost_add_track * sum{(i,j) in LINES} distance[i,j]*tracks_exist[i,j]    # Take away cost of existing tracks
  + cost_new_line * sum{(i,j) in LINES} distance[i,j]*x_line_exist[i,j]     # Cost of paving new lines from scratch
  - cost_new_line * sum{(i,j) in LINES} distance[i,j]*line_exist[i,j]       # Take away cost of existing lines
  ;
  
###################################################
# CONSTRAINTS

# Number of reloading buildings at station i must be greater than
# or equal to number of existing buildings at station i
subject to cant_destroy_reloading_bldgs {i in STATIONS}:
  x_num_reload_bldg[i] >= reload_bldg_exist[i];
  
# Number of tracks from station i to station j plus number of tracks
# from station j to station i must be greater than or equal to number of 
# existing tracks between stations i and j
subject to cant_destroy_tracks {(i,j) in LINES}:
  x_num_tracks[i,j] + x_num_tracks[j,i] >= tracks_exist[i,j];
  
# If line existed between stations i and j in sourceal set up, it must still exist at end
subject to cant_destroy_lines {(i,j) in LINES}:
  x_line_exist[i,j] >= line_exist[i,j];  
  
# Tracks can only handle track_capacity units
subject to cant_exceed_track_capacity {(i,j) in ARCS}:
  sum{(s,d) in DELIVS} x_num_units[s,d,i,j] <= track_capacity * x_num_tracks[i,j];

# Reloading buildings can only handle load_per_building incoming units
# Todo: Needs to handle units that come from source
subject to cant_exceed_reloading_bldg_capacity {k in STATIONS}:
  sum{(s,d) in DELIVS, (i,j) in ARCS: j==k} x_num_units[s,d,i,j] <= load_per_building * x_num_reload_bldg[k];

# Source must have entire shipment volume sent out
subject to entire_shipment_sent {(source,dest) in DELIVS}:
  sum{(i,source) in ARCS} x_num_units[source,dest,i,source]
  - sum{(source,j) in ARCS} x_num_units[source,dest,source,j]
  = -volume[source,dest];

# Destination must have entire shipment come in
subject to entire_shipment_arrives {(source,dest) in DELIVS}:
  sum{(i,dest) in ARCS} x_num_units[source,dest,i,dest]
  - sum{(dest,j) in ARCS} x_num_units[source,dest,dest,j]
  = volume[source,dest];

# All other stations must have equal volume coming in and going out
subject to balanced_along_path {(source,dest) in DELIVS, k in STATIONS: k != source && k != dest}:
  sum{(i,k) in ARCS} x_num_units[source,dest,i,k]
  - sum{(k,j) in ARCS} x_num_units[source,dest,k,j]
  = 0;

# Can only have existing tracks if line_exist = 1
subject to bigM_existing_tracks_constraint {(i,j) in LINES}:
  tracks_exist[i,j] <= M * line_exist[i,j];

# Can only have tracks if x_line_exist = 1
# Need two constraints since x_line_exist[i,j] is only defined for i < j
subject to bigM_tracks_constraint {(i,j) in ARCS: i < j}:
  x_num_tracks[i,j] <= M * x_line_exist[i,j];
subject to bigM_tracks_constraint2 {(i,j) in ARCS: i > j}:
  x_num_tracks[i,j] <= M * x_line_exist[j,i];
  