#!/usr/bin/perl -w
#
# APRS-Based Rotor Controller
# (C) Andrew Koenig, KE5GDB, 2015
#
# Modified by Kirk Kendrick, KK2Z:
#    Jul 2016 Add serial processing for use in BLT-45 HAB tracking
#    Oct 2017 Added Tk graphical environment & made multi-threaded
#    Jun 2018 Restructured multi-threading
#
# Calculations for balloon azimuth & elevation adapted from work done by KT5TK
# in APRSantennaPointer.PL
# detailed info from:
# http://www.satcom.co.uk/article.asp?article=29&section=2
# Look at the javascript source code from:
# http://www.satcom.co.uk/article.asp?article=1

use strict;
use warnings;

use threads;
use Thread::Queue;
use Time::Format;

use Tk;
use Tk::Dialog;
use Tk::Entry;
use Tk::Label;
use Tk::Scrollbar;
use Tk::Text;
use Tk::ROText;
use Tk::Menu;
use Tk::Frame;
use Tk::DialogBox;
use Tk::Menubutton;
use Tk::Button;
use Tk::Radiobutton;
use Tk::Toplevel;
use Tk::Optionmenu;
use Tk::NoteBook;

use Ham::APRS::FAP qw(parseaprs direction distance);
use Ham::APRS::IS;
use Math::Trig;
use Math::Round;
use IO::Socket::INET;
use File::Tail;
use Config;
use Config::Simple;

use Data::Dumper;       # Data Dumper

########
## POSIX or Win32?
BEGIN {
	my $OS_win = ($^O eq "MSWin32") ? 1 : 0;
	if ($OS_win) {
		print "Loading Windows Win32::Serial module\n";
		eval "use Win32::SerialPort";
		die "$@\n" if ($@);
	} else {
		print "Loading Unix Device::Serial module\n";
		eval "use Device::SerialPort";
		die "$@\n" if ($@);
	}
}	

############ Initialize variables
my $version = "3.4";
my $lupdate = "Jun/10/2018";
my $INI_file = "aprs_rotor.ini";

my $status_msg :shared = ' '; # send messages from all threads to UI

my ($cfg,$DoAPRSIS,$DoAPRX,$DoSerial,$DoSTDIN,$DoUSR,$DoRotor,$DoAutostart,$DoRS,$RotorSelected);
my ($mylat,$mylon,$myalt,$mycall) = (0,0,0,'NOCALL');
my ($GSb1_text,$GSb1_lat,$GSb1_lon,$GSb1_alt);
my ($GSb2_text,$GSb2_lat,$GSb2_lon,$GSb2_alt,$GSb3_text,$GSb3_lat,$GSb3_lon,$GSb3_alt);
my (@ballooncalls,$PST_RotorIP,$PST_RotorPort,$PST_RotorProtocol,$USR_RotorIP,$USR_RotorPort,$USR_RotorProtocol);
my ($RotorIP,$RotorPort,$RotorProtocol,$RadioIP,$RadioPort,$RadioProtocol,$APRX_File);
my ($databits,$baud,$parity,$stopbits,$handshake,$Win32_Port,$POSIX_Port);

my ($thr_aprsis, $thr_aprx, $thr_serial, $thr_stdin, $thr_usr) = (0,0,0,0,0);
my ($last_DoAPRSIS,$last_DoUSR,$last_DoAPRX,$last_DoSerial,$last_DoSTDIN,$last_DoRotor) = (0,0,0,0,0,0); # none currently running
my $is = 0; 

# math calculation variables
my ($alt,$lat,$lon,$highest_alt) = (0,0,0,0);
my ($rotorelevation,$rotorazimuth,$direction,$elevation,$distance_km) = (0,0,0,0,0);

# corresponding display values
my ($d_mylat, $d_mylon, $d_myalt, $d_mycall) = ('0','0','0','NOCALL');
my ($d_alt,$d_lat,$d_lon,$d_highest_alt) =('0','0','0','0');
my ($d_rotorelevation,$d_rotorazimuth,$d_distance) =('0','0','0');
my ($d_pdate,$d_ptime,$d_packet) =('yy/mm/dd','hh:mm:ss',' ');
my $last_valid_alt = 0;				# initialize latest 'valid' balloon altitude to zero
my ($rotor_started,$rotor_socket,$radio_started,$radio_socket) = (0,0,0,0);
my ($ptime,$dif_time,$d_dif_time,$d_time)=(time(),0,"hh:mm:ss","hh:mm:ss");
my $stdin_redirected = (!(-t STDIN)); #-t is a file test on STDIN to see if a tty

########
# Quasi constant variables:
my $d_to_r = pi/180;	# degrees to rad conversion factor
my $r_to_d = 180/pi;	# rad to degrees conversion factor
my $A = 6378136.6;		# earth radius [m] at equator (largest)
my $B = 6356751.9;		# earth radius [m] at poles   (smallest)
my $F = 1/298.25642;	# earth flattening (source: http://en.wikipedia.org/wiki/Figure_of_the_Earth IERS 2003)
my $m_to_ft = 3.28084;	# meters to feet conversion factor
my $km_to_mi = $m_to_ft / 5.280;  # kilometers to mile conversion factor

my $p_type = {'udp'    => 'udp',
              'tcp'    => 'tcp'};
my @proto_type = keys %$p_type;

my $b_type = {'1200'    => '1200',
              '2400'    => '2400',
              '4800'    => '4800',
              '9600'    => '9600',
              '19200'   => '19200',
              '57600'   => '57600',
              '115200'  => '115200'  };
my @valid_baud = keys %$b_type;

my $s_type = {'Pi'      => 'Pi',
              'Normal'  => 'Normal'  };
my @screen_type = keys %$s_type;

my $u_type = {'English' => 'English',
              'Metric'  => 'Metric'  };
my @units_type = keys %$u_type;

my @default_ballooncalls = qw{W5ACM-9 KE5GDB-11};
my ($balloonfilter, $d_ballooncalls);
&update_ballooncalls;

my ($label_alt_ft, $label_alt_m) = ('Alt (ft)', 'Alt (m)');
my ($label_highest_alt_ft, $label_highest_alt_m) = ('Highest Alt (ft)', 'Highest Alt (m)');
my ($label_distance_km, $label_distance_mi) = ('Distance (km)', 'Distance (mi)');
my ($d_alt_convert, $alt_to_m, $d_distance_convert) = (1.0,1.0,1.0);
my $units = 'English';
my ($label_distance,$label_alt,$label_highest_alt);
&set_to_English;

### define fonts
my $font_main = "Arial";
my $font_rotor = "OCR B MT";
my $font_text = "OCR B MT";
my $font_main_size = 10;
my $font_rotor_size = 16;
my $font_text_size = 11;
my $screen_size = 'Normal'; # alternate is 'Normal'

#################################################
# Load current INI file...create if does not exist
&LoadINI;

#######  GET STARTED !! #########
my $start_time = time();
my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($start_time);				
my $d_date = sprintf("\n%04d/%02d/%02d %02d:%02d:%02d",
		1900 + $year, $mon + 1, $mday, $hour, $min, $sec); # note -- packet ends in CR

$SIG{INT} = \&interrupt; 	# force CTRL-C to go through exit handler

print "\n\tAPRS-Based Rotor Controller -- by KE5GDB";
print "\n\tVersion $version   $lupdate";

my $q = Thread::Queue->new();    # A new empty inter-thread communication queue

#############################################
# Create and Display GUI

my $mw = MainWindow->new();
$mw->protocol('WM_DELETE_WINDOW' => sub { &interrupt; exit; }); 

my $nb = $mw->NoteBook()->pack(-expand => 1, -fill => 'both');
my $p1 = $nb->add('page1', -label => '  Configure   ');
my $p2 = $nb->add('page2', -label => '  APRS_Rotor  ');

$mw->title ("\t\tAPRS-Based Rotor Controller -- Version $version $lupdate");

&set_screen;


$mw->configure(-menu       => my $menubar = $mw->Menu);
my $row;
my $col;
########### Menus ##############
# File Menu
my $file = $menubar->cascade(-label     => '~File', -tearoff   => 0        );
$file->command( -label => "Exit", -underline => 0, -command => \&interrupt );

# Help Menu
my $help = $menubar->cascade(-label => '~Help', -tearoff   => 0 );
$help->command( -label => "About", -command => \&mnabout );

#########
sub mnabout{
 my $dw = $mw->Dialog(
              -title     => 'About APRS-based Rotor Controller',
              -bitmap    => 'info',
              -buttons   => ["OK",],
              -text      => "Creator:  Andrew Koenig  KE5GDB\n".
							"Updator:  Kirk Kendrick  KK2Z\n".
                            "aprs_rotor.pl Ver $version\n ",
  );
  $dw->Show;
}

# Select modes to receive packets
#-- Frame title
my $f = $p1->Frame->pack(-fill => 'both');

$row=0;
$col=0;
my $btndump = $f->Button( -text => "Debug Dump", -command => sub { &DumpHash;1; }
                        )->grid(-row => $row, -column => $col++, -sticky => 'ew');

$f->Checkbutton( -text => 'APRS-IS',     -variable => \$DoAPRSIS    )->grid(-row => $row, -column => $col++, -sticky => 'w');

$f->Checkbutton( -text => 'USR Radio',   -variable =>  \$DoUSR      )->grid(-row => $row, -column => $col++, -sticky => 'w');

$f->Checkbutton( -text => 'Serial Port', -variable =>  \$DoSerial   )->grid(-row => $row, -column => $col++, -sticky => 'w');

$f->Checkbutton( -text => 'Rotor Output',-variable =>  \$DoRotor    )->grid(-row => $row, -column => $col++, -sticky => 'ew');

$f->Checkbutton( -text => 'Autostart',   -variable =>  \$DoAutostart)->grid(-row => $row, -column => $col++, -sticky => 'ew');

my $b_start = $f->Button( -text => "Start!", -command => 
                    sub { &start_processing; 1; }, -foreground   => 'red', -borderwidth  => 5
					)->	grid(-row => $row++, -column => $col, -sticky => 'ew');
my $btn_done = $f->Button( -text => "Exit", -command => sub { &interrupt }, -foreground => 'red', -borderwidth  => 5 
                    )->grid(-row => $row, -column => $col, -sticky => 'ew');

$row=1;
$col=1;
$f->Checkbutton( -text => 'APRX Logfile', -variable =>  \$DoAPRX )->grid(-row => $row, -column => $col++, -sticky => 'w');

my $APRXLogFile = $f->Scrolled('Entry', -textvariable => \$APRX_File, -background => 'light gray', 
                    -font => [-family => $font_text], -foreground   => 'black', -borderwidth  => 0, -width => 10
					)->grid(-row => $row, -column => $col++, -sticky => 'ew', -columnspan => 3);
 
#### Groundstation
$row=2;
$col=0;
my $l_GS = $f->Label(-text => 'Groundstation', -anchor => 'e', -justify => 'right'
                    )->grid(-row => $row++,   -column => $col+1, -sticky => 'e'  );
my $l_lat = $f->Label(-text => 'Latitude', -anchor => 'e', -justify => 'right'
	                )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $GSlat = $f->Entry( -textvariable => \$mylat, -validate=>'key', 
     -validatecommand =>sub{ return 0 if $_[0]=~/\D/; $d_mylat= sprintf("%8.2f",$mylat); 1 }, -invalidcommand => sub{ $mw->bell },
	 -font		  => [-family => $font_text,], -background   => 'light gray', -foreground   => 'black', -borderwidth  => 0,
	 -width        => 10, -relief       => 'sunken' )->grid(-row => $row, -column => $col+1, -sticky => 'ew'   );

my $btnGS1 = $f->Button( -textvariable => \$GSb1_text, -command => sub { 
     $mylat = $GSb1_lat; $mylon = $GSb1_lon; $myalt = $GSb1_alt; $d_mylat = $mylat; $d_mylon = $mylon; $d_myalt = $myalt; $1 }
	)->grid(-row => $row++, -column => $col+2, -sticky => 'ew');


my $l_lon = $f->Label(-text => 'Longitude', -anchor => 'e', -justify => 'right' 
   )->grid(-row => $row, -column => $col, -sticky => 'e');
my $GSlon = $f->Entry( -textvariable => \$mylon, -validate=>'key', 
     -validatecommand=>sub{	return 0 if $_[0]=~/\D/; $d_mylon= sprintf("%8.2f",$mylon); 1; }, -invalidcommand => sub{ $mw->bell },
	 -font => [-family => $font_text,], -background => 'light gray',-foreground => 'black', -borderwidth => 0, -width => 10,
	 -relief => 'sunken' )->grid(-row => $row, -column => $col+1, -sticky => 'ew'   );

my $btnGS2 = $f->Button( -textvariable => \$GSb2_text, -command => sub { 
       $mylat = $GSb2_lat; $mylon = $GSb2_lon; $myalt = $GSb2_alt; $d_mylat = $mylat; $d_mylon = $mylon; $d_myalt = $myalt; $1 }
	)->grid(-row => $row++, -column => $col+2, -sticky => 'ew');

my $l_alt = $f->Label(-text => 'Alt (m)', -anchor => 'e', -justify => 'right' )->grid(-row => $row, -column => $col, -sticky => 'e');
my $GSalt = $f->Entry( -textvariable => \$myalt, -font => [-family => $font_text,], -background   => 'light gray', -foreground => 'black',
	 -borderwidth  => 0, -width => 10, -relief => 'sunken' )->grid(-row => $row, -column => $col+1   );

my $btnGS3 = $f->Button( -textvariable => \$GSb3_text, -command => sub { 
       $mylat = $GSb3_lat; $mylon = $GSb3_lon; $myalt = $GSb3_alt; $d_mylat = $mylat; $d_mylon = $mylon; $d_myalt = $myalt; $1 }
	)->grid(-row => $row++, -column => $col+2, -sticky => 'ew');

my $l_aprs1 = $f->Label(-text => 'Call', -anchor => 'e', -justify => 'right' )->grid(-row => $row, -column => $col, -sticky => 'e');
my $GScall = $f->Entry( -textvariable => \$mycall, -font => [-family => $font_text,], -validate=>'key',
	 -validatecommand=>sub{1; return 0 if $_[0]=~/(?>[1-9][A-Z][A-Z]?+[0-9]|[A-Z][2-9A-Z]?[0-9])[A-Z]{1,4}+;/}, -invalidcommand => sub{ $mw->bell },
     -background => 'light gray', -foreground => 'black', -borderwidth => 0, -state	=> 'readonly', -width => 10, -relief => 'sunken'
	)->grid(-row => $row, -column => $col+1, -sticky => 'ew'   );	
my $btnNOCALL = $f->Button( -text => "Set GS to NOCALL", -command => sub { $mycall = 'NOCALL';1; }
    )->grid(-row => $row++, -column => $col+2, -sticky => 'ew');
 
my $APRS_call;
my $lb_add_button = $f->Button( -text =>  'Add to GS', -command => sub { $mycall = uc $APRS_call; $APRS_call = ''; 1;},
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');
my $l_aprs2 = $f->Label(-text => 'APRS_ID', -anchor => 'e', -justify => 'right' )->grid(-row => $row, -column => $col, -sticky => 'ew');
my $lb_entry = $f->Entry( -textvariable => \$APRS_call, -background => 'light gray', -foreground => 'black', -font => [-family => $font_text,],
	 -borderwidth  => 0, -width => 10, -relief => 'sunken' )->grid(-row => $row, -column => $col+1, -sticky => 'ew');
	
my $lb_clr_button = $f->Button( -text => 'Clear', -command => sub { $APRS_call = ''; 1;} )->grid(-row => $row++, -column => $col+2, -sticky => 'ew');

my $lb_Balloon = $f->Scrolled('Listbox', -height => 6, -width => 10, -font => [-family => $font_text,], -scrollbars => 'w', -selectmode => 'single'
	)->grid(-row => $row+1, -column => $col+1,  -rowspan	  => 3);
$lb_Balloon->insert('end',@ballooncalls);

my $lb_add_button2 = $f->Button( -text => 'Add to Balloon', -command => sub { 
    $lb_Balloon->insert("end", uc $APRS_call); $APRS_call = '';	@ballooncalls = $lb_Balloon->get(0,'end'); &update_ballooncalls;1;},
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $lb_del_button = $f->Button( -text => 'Delete', -command => sub { $lb_Balloon->
    delete($lb_Balloon->curselection) if (defined($lb_Balloon->curselection));	@ballooncalls = $lb_Balloon->get(0,'end'); &update_ballooncalls;1;},
	)->grid(-row => $row, -column => $col+2, -sticky => 'ew');
	

# -- Rotor setup -- enable and selected mode
$row=2;
$col=3;		 	 
my $l_rotor = $f->Label(-text => 'Rotor', -anchor => 'e', -justify => 'right' )->grid(-row => $row++,   -column => $col, -sticky => 'e');
my $l_rotorip = $f->Label(-text => 'rotor.ip', -anchor => 'e', -justify => 'right' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $l_rotorip2 = $f->Entry(-textvariable => \$RotorIP, -background   => 'light gray', -foreground   => 'black',	-font => [-family => $font_text],
	 -borderwidth  => 0, -width => 10, -relief => 'sunken' )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l_rotorport = $f->Label(-text => 'rotor.port', -anchor => 'e', -justify => 'right' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $l_rotorport2 = $f->Entry(-textvariable => \$RotorPort, -background => 'light gray', -foreground => 'black', -borderwidth => 0,
	-font => [-family => $font_text,], -width => 10, -relief => 'sunken' )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l_rotorproto = $f->Label(-text => 'rotor.protocol', -anchor => 'e', -justify => 'right' )->grid(-row => $row, -column => $col, -sticky => 'e');
my $l_rotorproto2 = $f->Optionmenu(-options => \@proto_type, -variable => \$RotorProtocol, -font => [-family => $font_text],-background => 'gray'
    )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $SetUSR = $f->Button( -text => 'Set to USR', -command => sub {
    $RotorIP = $USR_RotorIP; $RotorPort = $USR_RotorPort; $RotorProtocol = $USR_RotorProtocol; 1;} 
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $SetPST = $f->Button(-text => 'Set to PST', -command => sub {
	$RotorIP = $PST_RotorIP; $RotorPort = $PST_RotorPort; $RotorProtocol= $PST_RotorProtocol; 1;}
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

# -- Radio setup -- columns 0-2
my $l_radio = $f->Label(-text => 'Radio', -anchor => 'e', -justify => 'right')->grid(-row => $row++,   -column => $col, -sticky => 'e');
my $l_radioip = $f->Label(-text => 'radio.ip', -anchor => 'e', -justify => 'right' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $r_IP = $f->Entry(-textvariable => \$RadioIP,-background => 'light gray',-foreground => 'black',-borderwidth => 0,-width => 10,-relief => 'sunken'
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l_radioport = $f->Label(-text => 'radio.port', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $r_port = $f->Entry( -textvariable => \$RadioPort, -background => 'light gray',-foreground   => 'black',-font => [-family => $font_text,], 
	 -borderwidth  => 0,-width => 10, -relief => 'sunken' )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l_radioproto = $f->Label(-text => 'radio.protocol', -anchor => 'e', -justify => 'right' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $r_Proto = $f->Optionmenu(-options => \@proto_type, -variable => \$RadioProtocol,-font => [-family => $font_text,],-background => 'gray'
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');
$row=3;
$col=5;
my $lb_baud = $f->Label(-text => 'Baud rate ', -anchor => 'e', -justify => 'right')->grid(-row => $row, -column => $col, -sticky => 'ew');
my $o_baud = $f->Optionmenu(-options => \@valid_baud,-variable => \$baud, -background => 'gray',-font => [-family => $font_text,] 
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');
my $l_com1 = $f->Label(-text => 'Win32 COMport', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $e_com1 = $f->Entry(-textvariable => \$Win32_Port,-font	=> [-family => $font_text,], -background => 'light gray', -foreground   => 'black',
	 -borderwidth => 0, -width => 10, -relief => 'sunken' )->grid(-row => $row++, -column => $col+1, -sticky => 'ew' );
my $l_com2 = $f->Label(-text => 'POSIX Port', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $e_com2 = $f->Entry( -textvariable => \$POSIX_Port,-font => [-family => $font_text,], -background => 'light gray', -foreground => 'black',
	 -borderwidth  => 0, -width => 10, -relief => 'sunken' )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

$f->Checkbutton( -text => 'Set RS to LF', -variable =>  \$DoRS	)->grid(-row => $row++, -column => $col, -sticky => 'ew', -columnspan => 2);

my $l_RS = $f->Label(-text => 'Unix uses LF record separator: D710 also. Win32 uses CF-LF record separator.',-justify => 'left', -wraplength => '200',
    )->grid(-row => $row++, -column => $col, -sticky => 'ew', -columnspan => 2);

my $l_SS1 = $f->Label(-text => 'Screen Size', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $l_ss2 = $f->Optionmenu( -options => \@screen_type, -variable => \$screen_size, -command	=> [sub {&set_screen;1;}, 'First'],-background  => 'gray',
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l_units = $f->Label(-text => 'Units', -anchor => 'e', -justify => 'right' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $l_units2 = $f->Optionmenu(-options => \@units_type, -variable => \$units, -background   => 'gray',
	 -command => [sub {if($units eq 'English') {&set_to_English} else {&set_to_Metric	};1;}, 'First'],
     )->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

$row=16;
my $btn1 = $f->Button( -text => "! Reset !",-command => sub {unlink $INI_file; &InitINI; 1})->grid(-row => $row, -column => $col++, -sticky => 'ew');

$f->Checkbutton(-text => 'STDIN (Debug)', -variable =>  \$DoSTDIN )->grid(-row => $row,   -column => $col++, -sticky => 'e');

$row=17;
$col=4;
my $lb_blank = $f->Label(-text => ' ', -anchor => 'w', -justify => 'left' )->grid(-row => $row++, -column => 0, -sticky => 'ew');
my $stat = $f->Label(-textvariable => \$status_msg, -anchor => 'w', -justify => 'left' 
     )->grid(-row => $row, -column => 0, -sticky => 'ew', -columnspan => 6	);

# Set all rows and columns to "equal weight"
my ($columns,$rows) = $f->gridSize();
for (my $i=0;$i<$columns; $i++) {
	$f->gridColumnconfigure($i,-weight => 1, -pad => 2);
};
for (my $i=0;$i<$rows; $i++) {
	$f->gridRowconfigure($i,-weight => 1, -pad => 2);
};
################## Page 2 ######################
$row=0;
$col=0;
my $frm = $p2->Frame->pack(-fill => 'both');
my $btndump2 = $frm->Button( -text => "Debug Dump", -command => sub { &DumpHash;1; } )->grid(-row => $row, -column => 0, -sticky => 'ew');

$col=2;
my $l_time = $frm->Label(-textvariable => \$d_time, -justify => 'center',-font => [-family => $font_rotor, -size => $font_rotor_size]
	)->grid(-row => $row,   -column => 2, -columnspan => 2 	);
	

my $btn3 = $frm->Button( -text => "Exit", -command => sub { &interrupt },-foreground => 'red', -borderwidth  => 5
	)->grid(-row => $row++, -column => 5, -sticky => 'ew');
$col=0;
## Each mode switch on page 2 initiates and kills threads for each mode of operation
## 0ff-to-On => Call Mode Subroutine to start mode thread
## On-to-Off => Send KILL command to thread, detach, and let it die
my $c1 = $frm->Checkbutton(	-text => 'APRSIS',-variable =>  \$DoAPRSIS,	
      -command  => sub {&SubAPRSIS if ($last_DoAPRSIS != $DoAPRSIS); $last_DoAPRSIS = $DoAPRSIS; 1;},-state => 'normal',
	)->grid(-row => $row, -column => $col++, -sticky => 'e');
	
my $c2 = $frm->Checkbutton(	-text => 'USR Radio',-variable =>  \$DoUSR,
 	-command  => sub {&SubUSR if ($last_DoUSR != $DoUSR); $last_DoUSR = $DoUSR; 1;}, -state => 'normal',
	)->grid(-row => $row, -column => $col++, -sticky => 'ew');
my $c3 = $frm->Checkbutton( -text => 'Serial Port',	-variable =>  \$DoSerial,
			-command  => sub { &SubSerial if ($last_DoSerial != $DoSerial); $last_DoSerial = $DoSerial; 1;}, -state => 'disabled',
	)->grid(-row => $row, -column => $col++, -sticky => 'ew');

my $c4 = $frm->Checkbutton(	-text => 'STDIN(Debug)', -variable =>  \$DoSTDIN,
			-command  => sub { &SubSTDIN if ($last_DoSTDIN != $DoSTDIN); $last_DoSTDIN = $DoSTDIN; 1;}, -state => 'disabled',
	)->grid(-row => $row, -column => $col++, -sticky => 'e');

my $c5 = $frm->Checkbutton(	-text => 'APRX Logfile', -variable =>  \$DoAPRX,
			-command  => sub { &SubAPRX if ($last_DoAPRX != $DoAPRX); $last_DoAPRX = $DoAPRX; 1;}, -state => 'normal',
	)->grid(-row => $row, -column => $col++, -sticky => 'ew');

my $c6 = $frm->Checkbutton( -text => 'Rotor Output', -variable =>  \$DoRotor,
			-command  => sub { if ($last_DoRotor != $DoRotor) {$rotor_started = &SubRotor; $last_DoRotor = $DoRotor; } },
	)->grid(-row => $row, -column => $col++, -sticky => 'ew');
		

$row = 2;
$col = 0;
my $l_GS2 = $frm->Label(-text => 'BalloonCall', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
$col = 1;
my $l_ball3 = $frm->Label(-textvariable => \$d_ballooncalls, -anchor => 'w', -justify => 'left',-font => [-family => $font_text,], 
	)->grid(-row => $row,   -column => $col, -sticky => 'w' , -columnspan => 4	);

$row = 3;
$col = 0;

my $l_GScall = $frm->Label(-text => 'GroundCall' )->grid(-row => $row,   -column => $col, -sticky => 'e');
my $l_GS3 = $frm->Label(-textvariable => \$mycall, -font => [-family => $font_text,], -justify => 'left'
	)->grid(-row => $row++,   -column => $col+1, -sticky => 'ew'  );
	
my $l2 = $frm->Label(-text => 'Lat', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id2 = $frm->Label( -textvariable => \$d_mylat, -borderwidth  => 0, -font => [-family => $font_text,],-justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l3 = $frm->Label(-text => 'Lon', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id3 = $frm->Label(-textvariable => \$d_mylon,-borderwidth  => 0,-font => [-family => $font_text,], -justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l4 = $frm->Label(-textvariable => \$label_alt, -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id4 = $frm->Label(-textvariable => \$d_myalt,-borderwidth  => 0,-font => [-family => $font_text,],-justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

$row = 3;
$col = 2;
my $l_ball2 = $frm->Label(-text => 'Balloon',     -anchor => 'e', -justify => 'right')->grid(-row => $row++,   -column => $col, -sticky => 'e');
my $l5 = $frm->Label(-text => 'Lat', -anchor => 'e', -justify => 'right'	)->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id5 = $frm->Label(-textvariable => \$d_lat,	-borderwidth  => 0,	-font => [-family => $font_text,],-justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l6 = $frm->Label(-text => 'Lon', -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id6 = $frm->Label(-textvariable => \$d_lon,	-borderwidth  => 0,	-font => [-family => $font_text,],-justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');

my $l7 = $frm->Label(-textvariable => \$label_alt, -anchor => 'e', -justify => 'right')->grid(-row => $row,   -column => $col, -sticky => 'e');
my $id7 = $frm->Label(-textvariable => \$d_alt,	-borderwidth  => 0,	-font => [-family => $font_text,], -justify => 'left',-width => 10
	)->grid(-row => $row++, -column => $col+1, -sticky => 'ew');
$row=3;
$col=4;
my $l11 = $frm->Label(-textvariable => \$label_distance,  -justify => 'center')->grid(-row => $row++,   -column => $col);
my $id11 = $frm->Label(	-textvariable => \$d_distance, -borderwidth  => 0, -font => [-family => $font_text,], -justify => 'center',-width => 10
	)->grid(-row => $row++, -column => $col);

my $l9 = $frm->Label(-textvariable => \$label_highest_alt, -justify => 'center'	)->grid(-row => $row++,   -column => $col);
my $id9 = $frm->Label(-textvariable => \$d_highest_alt,	-borderwidth  => 0,	-font => [-family => $font_text,],-justify => 'center',	-width => 10
	)->grid(-row => $row++, -column => $col);

$row = 3;
$col = 5;
	
my $l13 = $frm->Label(-text => 'AZIMUTH', -justify => 'center')->grid(-row => $row++,   -column => $col);
my $id13 = $frm->Label(	-textvariable => \$d_rotorazimuth,-borderwidth  => 0,-font => [-family => $font_rotor, -size => $font_rotor_size],
		-justify => 'center', -width => 4 )->grid(-row => $row++, -column => $col);

my $l14 = $frm->Label(-text => 'ELEVATION', -justify => 'center')->grid(-row => $row++,   -column => $col);
my $id14 = $frm->Label(	-textvariable => \$d_rotorelevation,-borderwidth  => 0,	-font => [-family => $font_rotor, -size => $font_rotor_size],
		-justify => 'center',-width => 4 )->grid(-row => $row++, -column => $col);

$row=8;
$col = 0;
my $id1 = $frm->Label(	-textvariable => \$d_dif_time,-justify => 'left',-font => [-family => $font_rotor, -size => $font_rotor_size] #, -width => 10
	)->grid(-row => $row, -column => $col, -sticky => 'w');
my $l_packet = $frm->Label(-textvariable => \$d_packet, -justify => 'left',-anchor => 'w'
    )->grid(-row => $row++, -column => $col+1, -sticky => 'ew', -columnspan => 4	);
my $l_stat2 = $frm->Label(-text => 'Status:', -anchor => 'e', -justify => 'right'
	)->grid(-row => $row,   -column => $col, -sticky => 'e');
my $stat2 = $frm->Label(-textvariable => \$status_msg, -anchor => 'w', -justify => 'left'
	)->grid(-row => $row, -column => $col+1, -sticky => 'ew', -columnspan => 4	);

#			
# Set all rows and columns to "equal weight"
($columns,$rows) = $frm->gridSize();
for (my $i=0;$i<$columns; $i++) {
	$frm->gridColumnconfigure($i,-weight => 1, -pad => 2);
};
for (my $i=0;$i<$rows; $i++) {
	$frm->gridRowconfigure($i,-weight => 1, -pad => 2);
};
my $frmText = $p2->Frame->pack(-fill => 'both');
my $txt = $p2->Scrolled ('ROText',-height => 48,-font => [-family => $font_text, -size => $font_text_size],-wrap => 'none',)->pack( -fill => 'both');

$mw->repeat(1000, \&Process);  # check for packets every 1 second;
if ($stdin_redirected) {
	tie *STDOUT, 'Tk::Text', $txt;              # redirect STDOUT to Text Widget
	}
################## end of Tk setup

####### Main Loop
&start_processing if ($DoAutostart);

$mw->update();

# Output starting time
$start_time = time();			# Set start time
($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($start_time);

printf("\n%04d/%02d/%02d %02d:%02d:%02d UTC --- starting time ---", 
       1900 + $year, $mon + 1, $mday, $hour, $min, $sec);

my $filename = "logs\\packet-log-$start_time.txt";
open(my $log, '>', $filename) or die("Could not open file '$filename' $!");

printf $log ("%04d/%02d/%02d %02d:%02d:%02d UTC --- starting time ---\n", 
       1900 + $year, $mon + 1, $mday, $hour, $min, $sec);


MainLoop();
my $result=interrupt();
exit;
#############################
#######   Subroutines   #####
#############################
sub set_screen {
if ($screen_size eq 'Pi') {
	$mw->geometry("800x480+0+0");
	$mw->maxsize(800,480);
} else {
	$mw->geometry("1280x700+0+0");
	$mw->maxsize(0,0);
};
$mw->optionAdd('*font' => [-size => $font_main_size]);
$mw->raise();
$mw->update();
}
#####################
sub start_processing {
	&update_ballooncalls;
	&UpdateINI;
	$nb->raise('page2');
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	$mw->update();
	&SubRotor if ($DoRotor);		$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&SubAPRSIS if ($DoAPRSIS);		$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&SubUSR if ($DoUSR);			$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&SubAPRX if ($DoAPRX);			$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&SubSerial if ($DoSerial);		$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&SubSTDIN if ($DoSTDIN);		$mw->update();
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	&update_display;
	$last_DoAPRSIS = $DoAPRSIS;
	$last_DoUSR = $DoUSR;
	$last_DoSerial = $DoSerial;
	$last_DoSTDIN = $DoSTDIN;
	$last_DoAPRX = $DoAPRX;
	$last_DoRotor = $DoRotor;
	$mw->raise();
}
#################
sub SubRotor {
# Attempt to connect to rotor
if ($DoRotor) {
	$rotor_socket = new IO::Socket::INET (
		PeerAddr => $RotorIP,
		PeerPort => $RotorPort,
		Proto => 	$RotorProtocol
		) or die ("\nCannot connect to rotor! $!\n");
	$rotor_started = 1; 
	$status_msg = "Connected to rotor at $RotorIP $RotorProtocol socket $RotorPort...";
	print "\n$status_msg";
} else {
	$status_msg = "Rotor disabled";
	print "\n$status_msg";
};
1;
}
##################################################
## < FOR APRS-IS USAGE (SEE END OF SCRIPT TOO)> ##
sub SubAPRSIS {
if ($DoAPRSIS) {
#	if ($thr_aprsis != 0) {
#		$thr_aprsis	->kill('KILL');
#		select undef, undef, undef, 2;	# traditional 2 sec.
#		}
	$thr_aprsis = threads->create(
		sub {
			my $tid = threads->tid();
			$status_msg = "Starting subprocess $tid -- APRS-IS";
			print "\n$status_msg";
			$is = new Ham::APRS::IS('rotate.aprs.net:14580', 'NOCALL', 'pass' => '-1',			
											'appid' => 'KE5GDB APRS Rotor Controller', 
											'filter' => $balloonfilter);
			$is->connect('retryuntil' => 3) || die ("Failed to connect: $is->{error}");

			$SIG{PIPE} = "IGNORE";
			$SIG{'KILL'} = sub { 
				print "\nClosing APRS-IS connection...";
				if ($is->connected()) {
					$is->disconnect() || die "Failed to disconnect: $is->{error}";
					threads->exit(); 
					};
				};

			$status_msg = "Connected to APRS-IS servers! $balloonfilter";
			print "\n$status_msg";
			my $p = '\n';
			while(1) {
				select undef, undef, undef, 1;	# traditional 1/sec.
				$p = $is->getline_noncomment();
				next if (!defined $p);
				chomp $p;
				next if ($p eq "");			# skip blank lines
				$p = $p . "\n";
				$q->enqueue($p);
			}
		}
		);
} else {
	$thr_aprsis ->kill('KILL') ->detach();
	$status_msg = "APRSIS closed";
	print "\n$status_msg";
};
1;
}
###################################################
## <FOR USR IOT to Radio  USAGE > ##
sub SubUSR { ;
if ($DoUSR) {
	$radio_socket = new IO::Socket::INET (
			PeerAddr => $RadioIP,
			PeerPort => $RadioPort,
			Proto => $RadioProtocol
	) or die ("\nCannot connect to Radio -- $!\n");
	$radio_started = 1; 
	$status_msg = "Connected to Radio TNC at $RadioIP $RadioProtocol socket $RadioPort...";
	print "\n$status_msg";
	select undef, undef, undef, 1;	# traditional 1/sec.

	$thr_usr = threads->create(
		sub {
			my $tid = threads->tid();
			$status_msg = "Starting subprocess $tid -- USR IOT";
			print "\n$status_msg";
#			my $p = "";
# 			Attempt to connect to radio
			local $/ = '\x{0D}' if $DoRS;						
			$SIG{PIPE} = "IGNORE";
			$SIG{'KILL'} = sub { threads->exit(); };

			while(1) {
				my $p = "";
				$p = $radio_socket->getline;
				next if (!defined $p);
				chomp $p;
				next if ($p eq "");			# skip blank lines
				select undef, undef, undef, 0.2;	# traditional 5/sec.
				$p = $p . "\n";
				$q->enqueue($p);
			}
		}
	);
} else {
		$thr_usr	->kill('KILL') ->detach();
		$status_msg = "USR closed";
		print "\n$status_msg";
}
1;
};
#####################
## < APRX LOGFILE> ##
sub SubAPRX {
if ($DoAPRX) {
	$thr_aprx = threads->create(
		sub {
			my $tid = threads->tid();
			$thr_aprx = $tid;
			$status_msg = "Starting subprocess $tid -- APRX";
			print "\n$status_msg";
			$SIG{PIPE} = "IGNORE";
			$SIG{'KILL'} = sub { threads->exit(); };
			my $p = '';
			my $file=File::Tail->new($APRX_File);
			while (defined($p=$file->read)) {
				next if (!defined $p);
				chomp $p;
				next if ($p eq "");					# skip blank lines
				select undef, undef, undef, 0.5;	# traditional 2/sec.
				$p = $p . "\n";
				$q->enqueue($p);
			}
		}
	);
} else {
	$thr_aprx	->kill('KILL') ->detach();
	$status_msg = "APRX closed";
	print "\n$status_msg";
};
1;
}
#########################################
## <FOR Serial port to KISS TNC USAGE  ##
#
sub SubSerial {
	if ($DoSerial) {
	$thr_serial = threads->create(
		sub {
			my $tid = threads->tid();
			$status_msg = "Starting subprocess $tid -- Serial";
			print "\n$status_msg";
			
			my ($port,$ob)=(0,0);
			$port = $Win32_Port if ( $^O eq 'MSWin32' );
			$ob = Win32::SerialPort->new($port) if ( $^O eq 'MSWin32' );
			die "$@\nCan't open $port: $!" if ($@);

			$port = $POSIX_Port if ( $^O ne 'MSWin32' );
			$ob = Device::SerialPort->new($port, 1) if ( $^O ne 'MSWin32' );
			die "$@\nCan't open $port: $!" if ($@);

			$SIG{'KILL'} = sub { 
				print "\nClosing Serial connection...";
				$ob -> close or die ("Close failed: $!\n");
				undef $ob;  # closes port AND frees memory in perl
				threads->exit();
				};
			$status_msg = "Connected to Serial port...";
			print "\n$status_msg";

			$ob->databits("8");
			$ob->baudrate($baud);
			$ob->parity("none");
			$ob->stopbits(1);
			$ob->handshake("none");
			$ob->buffers( 4096, 4096 );
			$ob->write_settings;


			my $p ='';
			while (1) {
				$p = $ob -> input;
				next if (! defined($p));		# read failed....try again
				chomp $p;
				next if ($p eq "");			# skip blank lines
				select undef, undef, undef, 0.5;	# traditional 2/sec.
				$p = $p . "\n";
				$q->enqueue($p);
			}
		}
	);
} else {
	$thr_serial	->kill('KILL') ->detach();
	$status_msg = "Serial closed";
	print "\n$status_msg";
};
1;
}

#######################################
## < FOR <STDIN> OR FILE CONNECTION> ##
## simply redirect file or serial port to input. EOF terminates.
sub SubSTDIN {
	if ($DoSTDIN) {
	$thr_stdin = threads->create(
	   sub {
	   my $tid = threads->tid();
	   $status_msg = "Starting subprocess $tid -- STDIN";
	   print "\n$status_msg";
	   $SIG{PIPE} = "IGNORE";
	   $SIG{'KILL'} = sub { threads->exit(); };
	   while(my $p = <> ) {
				last if eof();     # needed if we're reading from a terminal
				next if (!defined $p);
			    chomp $p;
				next if ($p eq "");			# skip blank lines
				select undef, undef, undef, 1;	# traditional 1/sec.
				$p = $p . "\n";
				$q->enqueue($p);
	       }
		$q->enqueue(undef);
		
	    }
	);
} else {
	$thr_stdin	->kill('KILL') ->detach();
	$status_msg = "STDIN closed";
	print "\n$status_msg";
};
1;
}

###################################################
####### Process received packets
sub Process {

	while (($q->pending()) > 0) {
#		$| = 1;			# flush buffer
		my $packet = $q->dequeue();
		last if (!defined($packet));
		next if ($packet eq "\n");			# skip blank lines
		next if($packet =~ /PKWDPOS/); ## ignore D710 location packets ##
		# Parse the packet
		my %packetdata;
		chomp($packet);
		my $retval = parseaprs($packet, \%packetdata);
print "\npacket is: $packet";
		if ($retval == 1) {
			# Skip non-location packets
			next if($packetdata{'type'} ne "location");
			my $call = $packetdata{'srccallsign'};
		
			# if callsign is groundstation callsign, update groundstation location
			if( $call eq $mycall) {
				$mylat  = $packetdata{'latitude'};
				$mylon  = $packetdata{'longitude'};
				$myalt	= $packetdata{'altitude'} if exists $packetdata{'altitude'};
				$myalt	= 0 unless $myalt =~ m/[0-9]+/; # set altitude to zero if invalid or neg
				&update_display;
				$txt->insert('end',$d_packet);  # add packet to end of display array
				$status_msg = "Groundstation location updated";
				print "\n$status_msg";
				next;
			} else {
				#  only process packets if callsign is in list of balloon callsigns
				$call = $packetdata{'srccallsign'};
				my $match = 0;
				foreach $a ( @ballooncalls ){
						$match = 1 if(( $a eq $call ) or ( $a eq '*'));
				}
				next if( $match==0 );		# skip this packet if doesn't match one of the balloo
				# Set packet time -- note: time not available in APRS-IS or direct packets
				$ptime = time();
				($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($ptime);
			
				$d_ptime = sprintf("%02d:%02d:%02d",	$hour, $min, $sec); # note -- packet ends in CR
				$d_pdate = sprintf("%04d/%02d/%02d",	1900+$year, $mon+1, $mday); # note -- packet ends in CR
				$d_packet = "\n$d_pdate $d_ptime $packet";
				# update location data -- assume lat/lon are valid
				$lat	= $packetdata{'latitude'};
				$lon	= $packetdata{'longitude'};
				$alt	= $packetdata{'altitude'} if exists $packetdata{'altitude'};
				$alt	= 0 if not exists $packetdata{'altitude'};
				$alt	= 0 unless $alt =~ m/[0-9]+/;	# set to zero if value invalid
				$alt	= $last_valid_alt if ($alt==0);		# set to last valid altitude otherwise
				$last_valid_alt = $alt if ($alt>0);			# save new altitude
				$highest_alt 	= $alt if ($alt>$highest_alt);  # record highest altitude --> close to burst altitude

				# Do the calculations with the help of Ham::APRS::FAP
				$distance_km	= distance($mylon, $mylat, $lon, $lat);	# distance in km
				$direction	= direction($mylon,$mylat,$lon,$lat);

				# Calculating the Great circle angle (in [rad])
				my $Ngc = acos( sin($mylat*$d_to_r) * sin($lat*$d_to_r) + cos($mylat*$d_to_r) * 
								cos($lat*$d_to_r) * cos(($lon-$mylon)*$d_to_r));
				my $Ngc_d = $r_to_d * $Ngc; # just for better imagination

				# Interpolate the sea level at the given locations
				# See http://en.wikipedia.org/wiki/Earth_radius
				my $R1 = sqrt (( (( $A**2 ) * ( cos($mylat*$d_to_r)))**2 + (( $B**2 ) * ( sin($mylat*$d_to_r)))**2 )/
							(( $A*cos($mylat*$d_to_r) )**2 + ( $B*sin($mylat*$d_to_r) )**2  ));

				my $R2 = sqrt (( (( $A**2 ) * ( cos($lat * $d_to_r) ) )**2 +
						( ( $B**2 ) * ( sin($lat * $d_to_r) ) )**2    )/
						( ( $A * cos($lat * $d_to_r) )**2 + ( $B * sin($lat * $d_to_r) )**2	));

				$elevation = $r_to_d * atan((cos($Ngc) - ($myalt + $R1) / ( $alt + $R2 ) ) / sin($Ngc));
				$elevation = 0 if($elevation < 0);  # keep elevation non-negative
		
				$alt = round($alt); 				# keep precision until after calculations
				$rotorelevation = round($elevation);
				$rotorazimuth = round($direction);
				&update_display;
				$txt->insert('end',$d_packet);  # add packet to end of display array
				print "$d_packet" if (! $stdin_redirected);
			
				# log packet to logfile
				print $log "$d_packet";
				close $log;		# close log and reopen to append entries (don't loose entries if app crashes)
				select undef, undef, undef, 0.2;	# traditional 5/sec.
				open($log, '>>', $filename) or die ("Could not open file '$filename' $!");
		
				my $rtrCommand = " ";
				$rtrCommand = "<PST><AZIMUTH>$rotorazimuth</AZIMUTH></PST>" .
							"<PST><ELEVATION>$rotorelevation</ELEVATION></PST>\n" 	if ($RotorSelected eq 'pst');	# PSTrotator format
				$rtrCommand = "AZ $rotorazimuth EL $rotorelevation\n" 				if ($RotorSelected ne 'pst');	# EASYCOMM format		
				if ($DoRotor && $rotor_started) {
					my $size = $rotor_socket->send($rtrCommand);
					chomp($rtrCommand); $status_msg = "Command sent to rotor: $rtrCommand";
				} else {
					chomp($rtrCommand); $status_msg = "Rotor disabled -- $rtrCommand";
					};
				}
				print "\n$status_msg\n";
				}
		}
$start_time = time();
($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($start_time);				
$d_time = sprintf("%02d:%02d:%02d", $hour, $min, $sec); 

$dif_time = $start_time - $ptime;   #seconds since last packet
my $dif_min = int($dif_time/60);
my $dif_hrs = int($dif_min/60);
$d_dif_time = sprintf("%3d:%02d:%02d",$dif_hrs, $dif_min % 60,$dif_time % 60);

$mw->update();

};
#####################
## Force display update
sub update_display {
$d_myalt= sprintf("%6d",$myalt*$d_alt_convert);
$d_mylat= sprintf("%8.2f",$mylat);
$d_mylon= sprintf("%8.2f",$mylon);
$d_alt= sprintf("%6d",$alt*$d_alt_convert);
$d_lat= sprintf("%8.2f",$lat);
$d_lon= sprintf("%8.2f",$lon);
$d_highest_alt= sprintf("%6d",$highest_alt*$d_alt_convert);
$d_rotorelevation= sprintf("%4d",$rotorelevation);
$d_rotorazimuth= sprintf("%4d",$rotorazimuth);
$d_distance= sprintf("%6.1f",$distance_km*$d_distance_convert);
}
#####################
sub update_ballooncalls {
if (! @ballooncalls) {
	$balloonfilter = 'r/'.$mylat.'/'.$mylon.'/50';
	$d_ballooncalls = ' ';
} else {
	$balloonfilter = 'b';
	$balloonfilter = $balloonfilter . '/' . $mycall if ($mycall ne 'NOCALL');
	$d_ballooncalls = '';
	foreach $a ( @ballooncalls ){
		$balloonfilter  = $balloonfilter  . '/' . $a;
		$d_ballooncalls = $d_ballooncalls .' ' . $a;
		}
	}
}
#####################
sub set_to_English {
$units = 'English';
$label_alt = $label_alt_ft;
$label_highest_alt = $label_highest_alt_ft;
$alt_to_m = 1/$m_to_ft;
$d_alt_convert = $m_to_ft;

$label_distance = $label_distance_mi;
$d_distance_convert = $km_to_mi;
};
#####################
sub set_to_Metric {
$units = 'Metric';
$label_alt = $label_alt_m;
$label_highest_alt = $label_highest_alt_m;
$alt_to_m = 1.0;
$d_alt_convert = 1.0;

$label_distance = $label_distance_km;
$d_distance_convert = 1.0;
}
###############################
# Subroutine to reset INI file to initial values

sub LoadINI {		#Load INI file and initialize variables
&CreateINI if !(-f $INI_file);	# Create and initialize if doesn't exist

$cfg = new Config::Simple("aprs_rotor.ini");	

$DoAPRSIS = $cfg->param('do.aprsis');
$DoAPRX = $cfg->param('do.aprx');
$DoSerial = $cfg->param('do.serial');
$DoSTDIN = $cfg->param('do.stdin');
$DoUSR = $cfg->param('do.usr');
$DoRotor = $cfg->param('do.rotor');
$DoAutostart = $cfg->param('do.autostart');

$DoRS = $cfg->param('do.record_separator');

$RotorSelected = $cfg->param('rotor.selected', 'USR');

$mylat = $cfg->param('groundstation.latitude');
$mylon = $cfg->param('groundstation.longitude');
$myalt = $cfg->param('groundstation.altitude');
$mycall = $cfg->param('groundstation.callsign');

$GSb1_text	 = $cfg->param('groundstation.b1_text');
$GSb1_lat	 = $cfg->param('groundstation.b1_lat');
$GSb1_lon	 = $cfg->param('groundstation.b1_lon');
$GSb1_alt	 = $cfg->param('groundstation.b1_alt');
							
$GSb2_text	 = $cfg->param('groundstation.b2_text');
$GSb2_lat	 = $cfg->param('groundstation.b2_lat');
$GSb2_lon	 = $cfg->param('groundstation.b2_lon');
$GSb2_alt	 = $cfg->param('groundstation.b2_alt');
							
$GSb3_text	 = $cfg->param('groundstation.b3_text');
$GSb3_lat	 = $cfg->param('groundstation.b3_lat');
$GSb3_lon	 = $cfg->param('groundstation.b3_lon');
$GSb3_alt	 = $cfg->param('groundstation.b3_alt');
							
@ballooncalls = $cfg->param('balloon.callsign');

$PST_RotorIP = $cfg->param('pst_rotor.ip');
$PST_RotorPort = $cfg->param('pst_rotor.port'); 
$PST_RotorProtocol = $cfg->param('pst_rotor.protocol');

$USR_RotorIP = $cfg->param('usr_rotor.ip');
$USR_RotorPort = $cfg->param('usr_rotor.port'); 
$USR_RotorProtocol = $cfg->param('usr_rotor.protocol');

$RotorIP = $cfg->param('rotor.ip');
$RotorPort = $cfg->param('rotor.port'); 
$RotorProtocol = $cfg->param('rotor.protocol');

$RadioIP = $cfg->param('radio.ip');
$RadioPort = $cfg->param('radio.port');
$RadioProtocol = $cfg->param('radio.protocol');

$APRX_File = $cfg->param('aprx.file');

$databits = $cfg->param('serial.databits');
$baud = $cfg->param('serial.baud');
$parity = $cfg->param('serial.parity');
$stopbits = $cfg->param('serial.stopbits');
$handshake = $cfg->param('serial.handshake');

$Win32_Port = $cfg->param('serial.win32_port');
$POSIX_Port = $cfg->param('serial.posix_port');
}


#######
# Subroutine to reset INI file to initial values
sub CreateINI {		#create new INI file

my $cfg = new Config::Simple(syntax=>'ini');				# Load configuration parameters

$cfg->param('groundstation.latitude', '29.258');
$cfg->param('groundstation.longitude', '-96.155');
$cfg->param('groundstation.altitude', '386');
$cfg->param('groundstation.callsign', 'KK2Z-9');

$cfg->param('groundstation.b1_text', 'Wharton');
$cfg->param('groundstation.b1_lat', '29.258');
$cfg->param('groundstation.b1_lon', '-96.155');
$cfg->param('groundstation.b1_alt', '31');
							
$cfg->param('groundstation.b2_text', 'SLC');
$cfg->param('groundstation.b2_lat', '41.71');
$cfg->param('groundstation.b2_lon', '-111.82');
$cfg->param('groundstation.b2_alt', '1415');
							
$cfg->param('groundstation.b3_text', 'Back44');
$cfg->param('groundstation.b3_lat', '30.88');
$cfg->param('groundstation.b3_lon', '-98.101');
$cfg->param('groundstation.b3_alt', '387');
$cfg->param('balloon.callsign',['W5ACM-9', 'KE5GDB-11']);

$cfg->param('do.record_separator', '0');
$cfg->param('do.aprsis',	 '1');
$cfg->param('do.aprx',  	 '0');
$cfg->param('do.serial',	 '0');
$cfg->param('do.stdin', 	 '0');
$cfg->param('do.usr',   	 '0');
$cfg->param('do.rotor', 	 '1');
$cfg->param('do.autostart',  '0');
$cfg->param('rotor.selected', 'pst');
$cfg->param('rotor.ip', '127.0.0.1');
$cfg->param('rotor.port', '8246');
$cfg->param('rotor.protocol', 'tcp');
$cfg->param('pst_rotor.ip', '192.168.42.255');
$cfg->param('pst_rotor.port', '12000');	
$cfg->param('pst_rotor.protocol', 'udp');
$cfg->param('usr_rotor.ip', '127.0.0.1');
$cfg->param('usr_rotor.port', '8246');	
$cfg->param('usr_rotor.protocol', 'tcp');
$cfg->param('radio.ip', '127.0.0.1');
$cfg->param('radio.port', '8245');
$cfg->param('radio.protocol', 'tcp');
$cfg->param('aprx.file', '/var/log/aprx/aprx-rf.log');
$cfg->param('serial.win32_port', 'COM4');
$cfg->param('serial.posix_port', '/dev/ttyUSB0');
$cfg->param('serial.databits', '8');
$cfg->param('serial.baud', '19200');
$cfg->param('serial.parity', "none");
$cfg->param('serial.stopbits', '1');
$cfg->param('serial.handshake', "none");

$cfg->write("$INI_file");
}
#####################
### Update INI file
sub UpdateINI {

my $cfg = new Config::Simple(syntax=>'ini');

$cfg->param('do.aprsis', $DoAPRSIS);
$cfg->param('do.aprx', $DoAPRX);
$cfg->param('do.serial', $DoSerial);
$cfg->param('do.stdin', $DoSTDIN);
$cfg->param('do.usr', $DoUSR);
$cfg->param('do.rotor', $DoRotor);
$cfg->param('do.autostart', $DoAutostart);
$cfg->param('do.record_separator', $DoRS);

$cfg->param('rotor.selected', $RotorSelected);

$cfg->param('groundstation.latitude', $mylat);
$cfg->param('groundstation.longitude', $mylon);
$cfg->param('groundstation.altitude', $myalt);
$cfg->param('groundstation.callsign', $mycall);

$cfg->param('groundstation.b1_text', $GSb1_text);
$cfg->param('groundstation.b1_lat', $GSb1_lat);
$cfg->param('groundstation.b1_lon', $GSb1_lon);
$cfg->param('groundstation.b1_alt', $GSb1_alt);

$cfg->param('groundstation.b2_text', $GSb2_text);
$cfg->param('groundstation.b2_lat', $GSb2_lat);
$cfg->param('groundstation.b2_lon', $GSb2_lon);
$cfg->param('groundstation.b2_alt', $GSb2_alt);

$cfg->param('groundstation.b3_text', $GSb3_text);
$cfg->param('groundstation.b3_lat', $GSb3_lat);
$cfg->param('groundstation.b3_lon', $GSb3_lon);
$cfg->param('groundstation.b3_alt', $GSb3_alt);

$cfg->param('pst_rotor.ip', $PST_RotorIP);
$cfg->param('pst_rotor.port', $PST_RotorPort);
$cfg->param('pst_rotor.protocol', $PST_RotorProtocol);

$cfg->param('usr_rotor.ip', $USR_RotorIP);
$cfg->param('usr_rotor.port', $USR_RotorPort);
$cfg->param('usr_rotor.protocol', $USR_RotorProtocol);

$cfg->param('rotor.ip', $RotorIP);
$cfg->param('rotor.port', $RotorPort);
$cfg->param('rotor.protocol', $RotorProtocol);

$cfg->param('radio.ip', $RadioIP);
$cfg->param('radio.port', $RadioPort);
$cfg->param('radio.protocol', $RadioProtocol);

$cfg->param('aprx.file', $APRX_File);

$cfg->param('serial.databits', $databits);
$cfg->param('serial.baud', $baud);
$cfg->param('serial.parity', $parity);
$cfg->param('serial.stopbits', $stopbits);
$cfg->param('serial.handshake', $handshake);

$cfg->param('serial.win32_port', $Win32_Port);
$cfg->param('serial.posix_port', $POSIX_Port);

$cfg->param('balloon.callsign', [@ballooncalls]);

$cfg->write("$INI_file");

}
####################

sub InitINI {        #reset INI values to defaults
# Groundstation Configuration -- Wharton Airport by default
$mylat =  '29.258';	 		# Latitude of rotor in Decimal Degrees -- Wharton Airport
$mylon =  '-96.155';	 		# Longitude of rotor in Decimal Degrees (west is negative!)
$myalt =  '386';				# Elevation of rotor} =  AMSL in meters  
$mycall =  'KK2Z-9';			# Change to local APRS ID to set new Groundstation Location

$GSb1_text = 'Wharton';
$GSb1_lat = '29.258';
$GSb1_lon = '-96.155';
$GSb1_alt = '31';

$GSb2_text = 'SLC';
$GSb2_lat = '41.71';
$GSb2_lon = '-111.82';
$GSb2_alt = '1415';

$GSb3_text = 'Back44';
$GSb3_lat = '30.88';
$GSb3_lon = '-98.101';
$GSb3_alt = '387';


# General constants
$DoRS =  '0';	# for MS "\x{0D}\n"

$DoAPRSIS =  '1';
$DoAPRX =    '0';
$DoSerial =  '0';
$DoSTDIN =   '0';
$DoUSR =     '0';

$DoRotor =   '1';
$DoAutostart =  '0';
@ballooncalls = @default_ballooncalls;
# Rotor configuration -- connect to ST1/2 USR IOT
$RotorIP =  '192.168.42.46';			# IP address '192.168.42.46' of rotor interface
$RotorPort =  '8246';				# port of rotor interface 
$RotorProtocol =  'tcp';
$RotorSelected = 'usr';

# PSTRotor configuration -- connect to PSTrotator
$PST_RotorIP =  '192.168.42.255';	# IP address of rotor [127.0.0.1] (rotctld)
$PST_RotorPort =  '12000';			# port of pstrotator [12000]
$PST_RotorProtocol =  'udp';

# USR Rotor configuration -- connect to ST1/2 USR IOT
$USR_RotorIP =  '192.168.42.46';		# IP address '192.168.42.46' of rotor interface
$USR_RotorPort =  '8246';			# port of rotor interface 
$USR_RotorProtocol =  'tcp';

# Radio USR IOT
$RadioIP =  '192.168.42.45';			# IP address 192.168.42.45 of rotor interface
$RadioPort =  '8245';				# port for tcp socket to radio interface
$RadioProtocol =  'tcp';			# 'udp' for pstrotator...'tcp' for usr iot

# APRX LOGFILE
$APRX_File =  '/var/log/aprx/aprx-rf.log';

# KISS TNC Serial Interface
$Win32_Port =  'COM4';
$POSIX_Port =  '/dev/ttyUSB0';
$databits =  '8';
$baud =  '19200';
$parity =  "none";
$stopbits =  '1';
$handshake =  "none";

};
###############  DEBUG ROUTINES BELOW  ################

#### debug output of hash structure
sub DumpHash {
print "\n\n===== \%C =====\n";

print "\nmylat:\t$mylat / $d_mylat";
print "\nmylon:\t$mylon / $d_mylon";
print "\nmyalt:\t$myalt / $d_myalt";
print "\nmycall:\t$mycall";

print "\nalt:\t$alt / $d_alt";
print "\nlat:\t$lat / $d_lat";
print "\nlon:\t$lon / $d_lon";
print "\nhighest_alt:\t$highest_alt / $d_highest_alt";
print "\nrotorelevation:\t$rotorelevation / $d_rotorelevation";
print "\nrotorazimuth:\t$rotorazimuth / $d_rotorazimuth";

print "\nDoRS:\t$DoRS";
print "\nDoAPRSIS:\t$DoAPRSIS / $last_DoAPRSIS";
print "\nDoAPRX:\t$DoAPRX / $last_DoAPRX";
print "\nDoSerial:\t$DoSerial / $last_DoSerial";
print "\nDoSTDIN:\t$DoSTDIN / $last_DoSTDIN";
print "\nDoUSR:\t$DoUSR / $last_DoUSR";
print "\nDoRotor:\t$DoRotor / $last_DoRotor";
print "\nDoAutostart:\t$DoAutostart";
print "\nRotorIP:\t$RotorIP";
print "\nRotorPort:\t$RotorPort";
print "\nRotorProtocol:\t$RotorProtocol";
print "\nRotorSelected:\t$RotorSelected";
print "\nPST_RotorIP:\t$PST_RotorIP";
print "\nPST_RotorPort:\t$PST_RotorPort";
print "\nPST_RotorProtocol:\t$PST_RotorProtocol";
print "\nUSR_RotorIP:\t$USR_RotorIP";
print "\nUSR_RotorPort:\t$USR_RotorPort";
print "\nUSR_RotorProtocol:\t$USR_RotorProtocol";
print "\nRadioIP:\t$RadioIP";
print "\nRadioPort:\t$RadioPort";
print "\nRadioProtocol:\t$RadioProtocol";
print "\nAPRS_File:\t$APRX_File";
print "\nWin32_Port:\t$Win32_Port";
print "\nPOSIX_Port:\t$POSIX_Port";
print "\ndatabits:\t$databits ";
print "\nbaud:\t$baud";
print "\nparity:\t$parity";
print "\nstopbits:\t$stopbits";
print "\nhandshake:\t$handshake";

print "\nd_pdate:\t$d_pdate";
print "\nd_packet:\t$d_packet";
print "\nstatus_msg:\t$status_msg";

print "\nBalloon Calls: @ballooncalls\nBalloon Filter List: $balloonfilter\n";
print "\nPacket time: $ptime / $d_ptime";
print "\nLast Packet: $dif_time / $d_dif_time";
print "\n===============\n";
}
################


#=======================================

sub interrupt {
	print STDERR "\nEXIT...\n";
	$status_msg = "\nKilling subprocesses...";

	print "\nKilling subprocesses...";
	$thr_aprsis	->kill('KILL') if (($DoAPRSIS) && ($thr_aprsis != 0));
	$thr_aprx	->kill('KILL') if (($DoAPRX) && ($thr_aprx != 0));
	$thr_serial	->kill('KILL') if (($DoSerial) && ($thr_serial != 0));
	$thr_stdin	->kill('KILL') if (($DoSTDIN) && ($thr_stdin != 0));
	$thr_usr	->kill('KILL') if (($DoUSR) && ($thr_usr != 0));
	select undef, undef, undef, 0.5;	# traditional 2/sec.
	
	print "\nClosing log file...$log";
	$status_msg = "\nClosing log file...$log";
	close $log;

	print "\nClosing Rotor Socket...";
	$status_msg = "\nClosing Rotor Socket...$log";
	$rotor_socket->close() if ($rotor_started != 0);
	select undef, undef, undef, 1.5;

	print "\nClosing Radio Socket...";
	$status_msg = "\nClosing Radio Socket...$log";
	$radio_socket->close() if ($radio_started != 0);
	select undef, undef, undef, 1.5;
	
	print "\nClosing packet queue...";
	$status_msg = "\nClosing packet queue...$log";
	$q->end();
	
	exit;  # or just about anything else you'd want to doa
	
}
### Saved Routines 
		
#### debug output of whole structure
#		while (my ($key, $value) = each(%packetdata)) {
#			print "$key: $value\n";
#		}
####
