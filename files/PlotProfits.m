%picking a distribution function
g=@(x) betapdf(x,1.05,10);
G=@(x) betacdf(x,1.05,10); 

%setting cutoff defining functions
c1=@(Delta) fsolve(@(t) (1-2*G(t))./g(t)-t-Delta,0.001);
c2=@(Delta) fsolve(@(t) (1-2*G(t))./g(t)-t+Delta,0.001);

%defining the profit function
profit=@(c) ((1-G(c)).^2+G(c).^2)./g(c);

%calculating values for plotting: [0,0.12] space is to have a nice picture,
%with no numerical problems due to c1 being too close to 0
vals=[];
for i=1:100;
vals=[vals;[0.12*i/100,c1(0.12*i/100),c2(0.12*i/100)]];
c1=@(Delta) fsolve(@(t) (1-2*G(t))./g(t)-t-Delta,vals(i,2));
end;
vals=[vals profit(vals(:,2)) profit(vals(:,3))];

%plotting
figure1 = figure;
axes1 = axes('Parent',figure1);
xlim(axes1,[0 0.12]);
ylim(axes1,[0 0.15]);
box(axes1,'on');
hold(axes1,'all');
title('Profit');

plot1 = plot(vals(:,1),[vals(:,[4:5 1])],'Parent',axes1);
set(plot1(1),'DisplayName','Good 1 on front page');
set(plot1(2),'DisplayName','Good 2 on front page');
set(plot1(3),'DisplayName','Show both');
xlabel('{\Delta}');
legend1 = legend(axes1,'show');
set(legend1,'Location','SouthEast');

