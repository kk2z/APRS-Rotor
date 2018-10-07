#!/usr/bin/perl -w
#
# APRS-Based Rotor Controller
# (C) Andrew Koenig, KE5GDB, 2015
#
# Modified by Kirk Kendrick, KK2Z, 2016 for use in BLT-45 HAB tracking
#
# Calculations for balloon azimuth & elevation adapted from work done by KT5TK
# in APRSantennaPointer.PL
#
use strict;
use warnings;

use Ham::APRS::FAP qw(parseaprs direction distance);
use Ham::APRS::IS;
use Math::Trig;
use Math::Round;
use IO::Socket::INET;

$SIG{INT} = \&interrupt; 	# force CTRL-C to go through exit handler

print "\n\tAPRS-Based Rotor Controller -- by KE5GDB\n";

# Groundstation Configuration
my $mylat = 29.258;	 			# Latitude of rotor in Decimal Degrees -- Wharton Airport
my $mylon = -96.155;	 			# Longitude of rotor in Decimal Degrees (west is negative!)
my $myalt = 386;				# Elevation of rotor, AMSL in meters  
my $mycall = "KK2Z-9";			# Callsign of ground station

#  Callsigns of trackers on balloon -- will position to ANY that are seen
my @ballooncalls = ('W5ACM-9','KG5MCU-9','N5SBN-14','KF5JRE-10');        # make list like ('AB5CD','W5ACM-9','xxx')

print "\nGround Station:",
      "\n\t$mycall",
      "\nBalloon callsigns:";

#  Build a filter list containing the Ground Station callsign and each balloon callsign
my $balloonfilter = 'b/' . $mycall;
foreach $a ( @ballooncalls ){
	$balloonfilter = $balloonfilter . '/' . $a;
	print "\n\t$a"
}
my $last_valid_alt = 0;				# initialize latest 'valid' balloon altitude to zero
my $highest_alt = 0;				# initialize highest 'valid' balloon altitude to zero

# APRS-IS Settings
my $aprsCall = "NOCALL";
my $aprsPass = "";

# Rotor configuration -- connect to PSTrotator
my $rotorIP = "192.168.42.255";	# IP address of rotor [127.0.0.1] (rotctld)
my $rotorPort = 12000;			# Port of pstrotator [12000]
my $rateLimit = 0;				# Rate limit rotor updates [30]

# Attempt to connect to rotor
my $socket = new IO::Socket::INET (
	PeerHost => $rotorIP,
	PeerPort => $rotorPort,
	Proto => 'udp',
	) or die "\nCannot connect to rotor! $!\n";
print "\n\nConnected to rotor!";

# Quasi constant variables:
my $d_to_r = pi/180;	# degrees to rad conversion factor
my $r_to_d = 180/pi;	# rad to degrees conversion factor
my $A = 6378136.6;		# earth radius [m] at equator (largest)
my $B = 6356751.9;		# earth radius [m] at poles   (smallest)
my $F = 1/298.25642;	# earth flatening (source: http://en.wikipedia.org/wiki/Figure_of_the_Earth IERS 2003)
my $m_to_ft = 3.28084;	# meters to feet conversion factor

# Set start time
my $start_time = time();

# Output starting time

my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($start_time);
printf("\n%04d/%02d/%02d %02d:%02d:%02d UTC --- starting time ---", 
       1900 + $year, $mon + 1, $mday, $hour, $min, $sec);

my $filename = "packet-log-$start_time.txt";
open(my $log, '>', $filename) or die "Could not open file '$filename' $!";
printf $log ("%04d/%02d/%02d %02d:%02d:%02d UTC --- starting time ---\n", 
       1900 + $year, $mon + 1, $mday, $hour, $min, $sec);

###################################################

## <UNCOMMENT THESE LINES FOR APRX LOGFILE> ##
#use File::Tail;
#$file=File::Tail->new("/var/log/aprx/aprx-rf.log");
#while (defined(my $packet=$file->read)) {
## </UNCOMMENT> ##

###################################################

## <UNCOMMENT THESE LINES FOR <STDIN> OR FILE CONNECTION> ##
## simply redirect file or serial port to input. EOF terminates.
#while(my $packet = <>) {
#	next if (!defined $packet);
## </UNCOMMENT> ##

###################################################

## <UNCOMMENT THESE LINES FOR APRS-IS USAGE (SEE END OF SCRIPT TOO)> ##
my $is = new Ham::APRS::IS('rotate.aprs.net:14580', $aprsCall, 'passcode' => $aprsPass, 'appid' => 'KE5GDB APRS Rotor Controller', filter => "$balloonfilter");
$is->connect('retryuntil' => 3) || die "Failed to connect: $is->{error}";
print "\nConnected to APRS-IS servers!\n";
while(1) {
   my $packet = $is->getline_noncomment();
   next if (!defined $packet);
   $packet = $packet . "\n";
## </UNCOMMENT> ##

###################################################

## <UNCOMMENT THESE LINES FOR KISS TNC USAGE (SEE END OF SCRIPT TOO)> ##
#
## UNCOMMENT these 3 lines for Windows
#use Win32::SerialPort;
#my $cfgfile = "COM1_aprs.cfg";
#my $ob = Win32::SerialPort->start ($cfgfile) or die "Can't start $cfgfile\n";
#
## UNCOMMENT these 3 lines for Linux
#use Device::SerialPort;
#my $port = '/dev/ttyUSB0';
#my $ob = Device::SerialPort->new($port, 1)|| die "Can't open $port: $!";
#   
#my $data = 		$ob->databits(8);
#my $baud = 		$ob->baudrate(19200);
#my $parity = 	$ob->parity("none");
#my $stop = 		$ob->stopbits(1);
#my $hshake = 	$ob->handshake("none");
#$ob->buffers( 4096, 4096 );
#$ob->write_settings;
#
#print "\nConnected to TNC...\n\n";
#
#my $packet;
#while (1) {
#    select undef, undef, undef, 0.2;	# traditional 5/sec.
#    $packet = $ob -> input;
#    next if (! defined($packet));		# read failed....try again
#    next if ($packet eq "");			# skip blank lines
#
## </UNCOMMENT> ##
###################################################

   # flush buffer
   $| = 1;

   # check for $PKWDPOS packets -- output by D710 every second to give location of D710
   next if($packet =~ /PKWDPOS/); ## just ignore them ##

# removed substr calc below....leave packet "whole"....need to talk to Andrew about this logic
#	# Cut it down to just the packet
#	if(!defined $packet) {
#		my $packet = substr $packet, 36;
#	}

	# Parse the packet
	my %packetdata;
	my $retval = parseaprs($packet, \%packetdata);

	if ($retval == 1) {
		# Skip non-location packets
		next if($packetdata{'type'} ne "location");
		
#### debug output of whole structure
#		while (my ($key, $value) = each(%packetdata)) {
#			print "$key: $value\n";
#		}
####
		my $call = $packetdata{'srccallsign'};
		
		# if callsign is groundstation callsign, update groundstation location
		if( $call eq $mycall) {
			$mylat  = $packetdata{'latitude'};
			$mylon  = $packetdata{'longitude'};

			$myalt	= $packetdata{'altitude'} if exists $packetdata{'altitude'};
			$myalt	= 0 unless $myalt =~ m/[0-9]+/; # set altitude to zero if invalid or neg
			next;
		} else {

		#  only process packets if callsign is in list of balloon callsigns
		$call = $packetdata{'srccallsign'};
		my $match = 0;
		foreach $a ( @ballooncalls ){
			$match = 1 if( $a eq $call );
		}
		next if( $match==0 );		# skip this packet if doesn't match one of the balloo

		# update location data -- assume lat/lon are valid
		my $lat	= $packetdata{'latitude'};
		my $lon	= $packetdata{'longitude'};

		my $alt;
		$alt	= $packetdata{'altitude'} if exists $packetdata{'altitude'};
		$alt	= 0 if not exists $packetdata{'altitude'};
		$alt	= 0 unless $alt =~ m/[0-9]+/;	# set to zero if value invalid
		$alt	= $last_valid_alt if ($alt==0);		# set to last valid altitude otherwise
		$last_valid_alt = $alt if ($alt>0);			# save new altitude
		$highest_alt 	= $alt if ($alt>$highest_alt);  # record highest altitude --> close to burst altitude

		my $comment;
		$comment = $packetdata{'comment'} if exists $packetdata{'comment'};
		$comment = "<no comment>" if not exists $packetdata{'comment'};

		my $symtable = $packetdata{'symboltable'};
		my $symcode  = $packetdata{'symbolcode'};
	
		# Do the calculations with the help of Ham::APRS::FAP
		my $distance_km	= distance($mylon, $mylat, $lon, $lat);	# distance in km
		my $distance_m	= $distance_km * 1000;  					# convert km to m
		my $direction	= direction($mylon,$mylat,$lon,$lat);

		# detailed info from:
		# http://www.satcom.co.uk/article.asp?article=29&section=2

		# Look at the javascript source code from:
		# http://www.satcom.co.uk/article.asp?article=1

		# Calculating the Great circle angle (in [rad])
		my $Ngc = acos( sin($mylat*$d_to_r) * sin($lat*$d_to_r) + cos($mylat*$d_to_r) * cos($lat*$d_to_r) * cos(($lon-$mylon)*$d_to_r));
		my $Ngc_d = $r_to_d * $Ngc; # just for better imagination

		# Interpolate the sea level at the given locations
			# See http://en.wikipedia.org/wiki/Earth_radius
		my $R1 = sqrt (( (( $A**2 ) * ( cos($mylat*$d_to_r)))**2 + (( $B**2 ) * ( sin($mylat*$d_to_r)))**2 )/
					     (( $A*cos($mylat*$d_to_r) )**2 + ( $B*sin($mylat*$d_to_r) )**2  ));

		my $R2 = sqrt (( (( $A**2 ) * ( cos($lat * $d_to_r) ) )**2 +
		    ( ( $B**2 ) * ( sin($lat * $d_to_r) ) )**2    )/
		    ( ( $A * cos($lat * $d_to_r) )**2 + ( $B * sin($lat * $d_to_r) )**2	));

		my $elevation = $r_to_d * atan((cos($Ngc) - ($myalt + $R1) / ( $alt + $R2 ) ) / sin($Ngc));
		$elevation = 0 if($elevation < 0);  # keep elevation non-negative
		
		$alt = round($alt); 				# keep precision until after calculations

		# Set packet time -- note: time not available in APRS-IS or direct packets
		my $time = time();
		($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($time);
		printf("\n%04d/%02d/%02d %02d:%02d:%02d %s",
			1900 + $year, $mon + 1, $mday, $hour, $min, $sec, $packet); # note -- packet ends in CR
		printf("\tLat    : %8.4f       MyLat   : %8.4f      Dist (km)  : %8.1f\n",$lat,$mylat,$distance_km);
		printf("\tLon    : %8.4f       MyLon   : %8.4f      Dir  (deg) : %8d\n",$lon,$mylon,$direction);
		printf("\tAlt    : %8d m     MyAlt   : %8d      Elev (deg) : %8d\n",$alt,$myalt,$elevation);
		printf("\tAlt    : %8d ft    Highest Alt -> %8d m | %8d ft <-\n",$alt*$m_to_ft,$highest_alt,$highest_alt*$m_to_ft);

				# log packet to logfile
		printf $log ("%04d/%02d/%02d %02d:%02d:%02d %s",
			1900 + $year, $mon + 1, $mday, $hour, $min, $sec, $packet);
		close $log;		# close log and reopen to append entries (don't loose entries if app crashes)
		select undef, undef, undef, 0.2;	# traditional 5/sec.
		open($log, '>>', $filename) or die "Could not open file '$filename' $!";
		
		my $rotorelevation = round($elevation);
		my $rotorazimuth = round($direction);
		
#		Output command to rotator -- EASYCOMM format		
#		my $command = "AZ $rotorazimuth EL $rotorelevation\n";

#		Output command to rotator -- PSTrotator format
		my $command = "<PST><AZIMUTH>$rotorazimuth</AZIMUTH></PST>" .
		              "<PST><ELEVATION>$rotorelevation</ELEVATION></PST>\n";

		print $socket "$command";
		my $size = $socket->send($command);
#		print "\tCommand sent to rotor: $command";

	}
   }
}

my $result=interrupt();
exit;

sub interrupt {
	print STDERR "EXIT due to control c!\n";
	$socket->close();
	close $log;

## UNCOMMENT FOR APRS-IS ##
	$is->disconnect() || die "Failed to disconnect: $is->{error}";
## </UNCOMMENT> ##

## UNCOMMENT FOR TNC ##
#	$ob -> close or die "Close failed: $!\n";
#	undef $ob;  # closes port AND frees memory in perl
## </UNCOMMENT> ##

	exit;  # or just about anything else you'd want to do
}
