using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Data;
using System.Diagnostics;
using System.Drawing;
using System.Linq;
using System.Linq.Expressions;
using System.Timers;
using Com.CodeGame.CodeWizards2016.DevKit.CSharpCgdk.Model;

namespace Com.CodeGame.CodeWizards2016.DevKit.CSharpCgdk
{
    public sealed class MyStrategy : IStrategy
    {

        static double WAYPOINT_RADIUS = 50.0D;
        static double SAFE_DISTANCE = 200D;

        static double LOW_HP_FACTOR = 0.35D;
        static double MEDIUM_HP_FACTOR = 0.50D;
        static double HIGH_HP_FACTOR = 0.80D;

        static int RETREAT_COOLDOWN = 30;
        static int RETREAT_COOLDOWN_ENEMY_WIZARDS = 50;

        static int BONUS_RESPAWN_INTERVAL = 2500;
        static int BONUS_PRERESPAWN_INTERVAL = 300;
        static double BONUS_RADIUS = 20;

        /**
         * Ключевые точки для каждой линии, позволяющие упростить управление перемещением волшебника.
         * <p>
         * Если всё хорошо, двигаемся к следующей точке и атакуем противников.
         * Если осталось мало жизненной энергии, отступаем к предыдущей точке.
         */

        Random random = new Random();

        LaneType lane;

        Point2D[] waypoints;

        private Point2D laneSwitchPoint = null;

        Wizard _myWizardPrev;
        World _myWorldPrev;
        Game _myGamePrev;
        Move _myMovePrev;

        private static StateType state = StateType.Idling;
        private static StateType prevState = StateType.Idling;

        static Wizard _myWizard;
        static World _myWorld;
        static Game _myGame;
        static Move _myMove;

        static int ticksToRetreat;

        private static int laneSwitchCooldown = 0;

        static List<Point2D> bonusPositions = new List<Point2D>
        {
            new Point2D(1200,1200),
            new Point2D(2800,2800),
        };

        private static double bonusPeekDistance => 1500;
        private static Point2D myPositionsBeforeBonusState;


        //private static int bonus1Cooldown = BONUS_RESPAWN_INTERVAL;
        //private static int bonus2Cooldown = BONUS_RESPAWN_INTERVAL;

        private static List<Point2D> GlobalPath { get; set; }

        private Point2D StartPosition { get; set; }
        private int HealthLooseSpeed { get; set; }

        private static int tickT = 0;
        private static int myTickT = 0;

        private static bool shouldUseGlobalPath = false;

        private static List<Tree> treeListToDestroy = new List<Tree>();

        public static Dictionary<Point2D, int> TowersGlobalCooldown = new Dictionary<Point2D, int>
        {
            {new Point2D(1687,50), 0},
            {new Point2D(2629,350), 0},

            {new Point2D(2070,1600), 0},
            {new Point2D(3097,1231), 0},

            {new Point2D(3650,2343), 0},
            {new Point2D(3950,1306), 0}
        };

        public int LooseHealthSpeed()
        {
            if (_myWizardPrev == null)
            {
                return 0;
            }

            var oldHp = _myWizardPrev.Life;
            var hp = _myWizard.Life;
            var maxHp = _myWizard.MaxLife;

            decimal speed = (oldHp - hp) / maxHp * 100;
            var percent = decimal.ToInt32(Math.Ceiling(speed));

            return percent;
        }

        public void Move(Wizard self, World world, Game game, Move move)
        {
            if (world.TickIndex == 0)
            {
                InitializeStrategy(self, game);
            }
            InitializeTick(self, world, game, move);

            //var buildings = _myWorld.Buildings.Where(i => i.Faction != _myWizard.Faction && i.GetDistanceTo(_myWizard)<=_myWizard.VisionRange).ToList();

            var goToPosition = (Point2D)null;
            var noTurnWhileWalking = false;

            if (_myGame.IsSkillsEnabled)
            {
                var level = _myWizard.Level;
                LearnSkill(level);
            }

            tickT = _myWorld.TickIndex;
            myTickT++;

            var tickDifference = tickT - myTickT; //получаем разницу в ходах после смерти волшебника

            UpdateTowerCooldown(tickDifference);
            UpdateTreeListToDestroy();

            if (tickT>=2501 && laneSwitchCooldown==0)
            {
                var lineWasSwitched = TrySwitchLine();
                if (lineWasSwitched)
                {
                    laneSwitchPoint = GetLaneSwitchPoint(lane);
                    laneSwitchCooldown = 3500;
                }
            }

            if (laneSwitchCooldown > 0)
            {
                laneSwitchCooldown--;
            }


            if (tickT < 150)
            {
                return;
            }



            prevState = state;

            state = StateType.Idling;

            if ( /*prevState == StateType.Walk &&*/ myPositionsBeforeBonusState != null &&
                                                    _myWizard.GetDistanceTo(myPositionsBeforeBonusState.GetX(),
                                                        myPositionsBeforeBonusState.GetY()) >= _myWizard.Radius*2)
            {
                state = StateType.Walk;
            }
            else
            {
                myPositionsBeforeBonusState = null;
            }
           
            
            if (prevState == StateType.GetBonus)
            {
                state = StateType.GetBonus;
            }

            if (laneSwitchCooldown==0 
                &&
                state != StateType.GetBonus
                &&
                ((bonusPositions[0].GetDistanceTo(_myWizard) <= bonusPeekDistance || bonusPositions[1].GetDistanceTo(_myWizard) <= bonusPeekDistance)
                &&
               ((tickT + BONUS_PRERESPAWN_INTERVAL) % BONUS_RESPAWN_INTERVAL == 0)
               ||
               (GetClosestBonus() != null && GetClosestBonus().GetDistanceTo(_myWizard) <= bonusPeekDistance)))
            {
                state = StateType.GetBonus;
                myPositionsBeforeBonusState = new Point2D(_myWizard.X, _myWizard.Y);
                if (myPositionsBeforeBonusState.GetDistanceTo(bonusPositions[0]) <= _myWizard.Radius * 3 ||
                    myPositionsBeforeBonusState.GetDistanceTo(bonusPositions[1]) <= _myWizard.Radius * 3)
                {
                    myPositionsBeforeBonusState = GetPreviousWaypoint();
                }
            }

            if (ticksToRetreat > 0)
            {
                state = StateType.Retreat;
                ticksToRetreat--;
            }

            var enemyWizards = GetNearestVisibleTargets(UnitType.Wizard) ?? new List<LivingUnit>();


            var enemyTowers = GetNearestVisibleTargets(UnitType.Building);
            //если не видно башен, используем глобальный кулдаун
            if (!enemyTowers.Any())
            {
                foreach (var cooldown in TowersGlobalCooldown)
                {
                    if (cooldown.Value!=-1 &&cooldown.Value<=10 && _myWizard.GetDistanceTo(cooldown.Key.GetX(), cooldown.Key.GetY()) <=
                        _myGame.GuardianTowerAttackRange + _myGame.WizardForwardSpeed*2)
                    {
                        state = StateType.Retreat;
                    }
                }
            }

            //если видно, проверяем задержку до выстрела
            if (enemyTowers.Any())
            {
                var closestTower = enemyTowers.OrderBy(i => i.GetDistanceTo(_myWizard)).FirstOrDefault();
                if (closestTower != null)
                {
                    var hitDistance = _myGame.GuardianTowerAttackRange;
                    var hitPoints = _myGame.GuardianTowerDamage;

                    var t = (closestTower as Building);
                    if (t != null)
                    {
                        hitDistance = t.AttackRange;
                        hitPoints = t.Damage;
                    }

                    //var ourWizards =
                    //    _myWorld.Wizards.Where(
                    //            i => i.Faction == _myWizard.Faction && i.GetDistanceTo(closestTower) <= hitDistance)
                    //        .ToList();

                    var ourForcesNearTower = new List<LivingUnit>();
                    ourForcesNearTower.AddRange(_myWorld.Wizards);
                    ourForcesNearTower.AddRange(_myWorld.Minions);
                    ourForcesNearTower =
                        ourForcesNearTower.Where(
                                i => i.Faction == _myWizard.Faction && i.GetDistanceTo(closestTower) <= hitDistance)
                            .ToList();

                    if (ourForcesNearTower.Any())
                    {
                        var candidate = ourForcesNearTower.Where(i => i.Life >= hitPoints).OrderBy(i => i.Life).FirstOrDefault();
                        if (candidate == null)
                        {
                            candidate = ourForcesNearTower.OrderByDescending(i => i.Life).FirstOrDefault();
                        }

                        var wizardCandidate = candidate as Wizard;
                        if (wizardCandidate != null)
                        {
                            if (wizardCandidate.IsMe)
                            {

                                var distanceToEscape = hitDistance * 1.05 - _myWizard.GetDistanceTo(closestTower);
                                if (distanceToEscape >= 0)
                                {

                                    var tower = closestTower as Building;
                                    if (tower != null)
                                    {
                                        var remainingCooldown = tower.RemainingActionCooldownTicks;

                                        var playerMaxSpeed = _myGame.WizardBackwardSpeed;

                                        var pathToRetreat = playerMaxSpeed * remainingCooldown;
                                        if (pathToRetreat <= distanceToEscape)
                                        {
                                            if (state == StateType.GetBonus && _myWizard.Life >= HIGH_HP_FACTOR)
                                            {

                                            }
                                            else
                                            {
                                                state = StateType.Retreat;
                                                ticksToRetreat = remainingCooldown + RETREAT_COOLDOWN;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }


                }

            }

            var visibleAllyWizards = GetNearestAllyUnits(UnitType.Wizard);
            var visibleAllyMinions = GetNearestAllyUnits(UnitType.Minion);
            //var visibleEnemyWizards = GetNearestVisibleTargets(UnitType.Wizard);
            if (enemyWizards.Count >= 2 &&
               (!visibleAllyMinions.Any() && !visibleAllyWizards.Any())
               && !(state == StateType.GetBonus && _myWizard.Life > HIGH_HP_FACTOR))
            {
                //if (visibleAllyWizards == null || visibleAllyWizards.Count <= 1)
                //{
                state = StateType.Retreat;
                if (ticksToRetreat < RETREAT_COOLDOWN_ENEMY_WIZARDS)
                {
                    ticksToRetreat = RETREAT_COOLDOWN_ENEMY_WIZARDS;
                }
                //}
            }

            var attackableWizards = GetNearestAttackableTargets(UnitType.Wizard);
            if (attackableWizards.Count >= 3)
            {
                state = StateType.Retreat;


                if (ticksToRetreat < RETREAT_COOLDOWN_ENEMY_WIZARDS)
                {
                    ticksToRetreat = RETREAT_COOLDOWN_ENEMY_WIZARDS;
                }
            }

            if (self.Life < self.MaxLife * LOW_HP_FACTOR || LooseHealthSpeed() >= 20)
            {
                state = StateType.Retreat;
                //if (_myWizard.Statuses.All(i => i.Type != StatusType.Shielded))
                //{
                //    _myMove.Action = ActionType.Shield;
                //}
            }


            //var ourBase =
            //    _myWorld.Buildings.FirstOrDefault(i => i.Type == BuildingType.FactionBase && i.Faction == _myWizard.Faction);
            //if (ourBase != null && _myWizard.GetDistanceTo(ourBase) >= _myWizard.VisionRange / 4 && _myWizard.GetDistanceTo(ourBase)<=2000)
            //{
            //    var enemyWizardsNearBase =
            //        _myWorld.Wizards.Where(
            //            i => i.Faction != _myWizard.Faction && i.GetDistanceTo(ourBase) <= _myWizard.VisionRange * 2).ToList();
            //    var enemyCreepsNearBase = _myWorld.Minions.Where(
            //            i => i.Faction != _myWizard.Faction && i.GetDistanceTo(ourBase) <= _myWizard.VisionRange * 2).ToList();

            //    var allyWizardNearBase = _myWorld.Wizards.Where(
            //            i => i.Faction == _myWizard.Faction && i.GetDistanceTo(ourBase) <= _myWizard.VisionRange * 2).ToList();
            //    var allyCreepsNearBase = _myWorld.Minions.Where(
            //          i => i.Faction == _myWizard.Faction && i.GetDistanceTo(ourBase) <= _myWizard.VisionRange * 2).ToList();

            //    var difference = enemyWizardsNearBase.Count - allyWizardNearBase.Count;

            //    if (difference>=2 || (difference>=1 && allyCreepsNearBase.Count<=1 && enemyCreepsNearBase.Count>=4))
            //    {
            //        state = StateType.Retreat;
            //    }
            //}


            //if (state == StateType.Retreat)
            //{
            //    var noTurningForward = target != null || visibleTargets.Any();

            //    GoTo(GetPreviousWaypoint(), noTurningForward);
            //}




            //var nearestBonus = GetClosestBonus();
            //if (state==StateType.GetBonus && ((nearestBonus != null &&
            //     nearestBonus.GetDistanceTo(_myWizard) >= _myWizard.Radius + BONUS_RADIUS + MapRadar.K) ||
            //    ((tickT - 5)%BONUS_RESPAWN_INTERVAL >= 0)))
            //{
            //    prevState = StateType.Idling;
            //    state = StateType.Walk;
            //}

            if (
                state == StateType.GetBonus &&

                ((_myWizard.GetDistanceTo(bonusPositions[0].GetX(), bonusPositions[0].GetY()) <= _myWizard.Radius + _myGame.BonusRadius
                ||
                _myWizard.GetDistanceTo(bonusPositions[1].GetX(), bonusPositions[1].GetY()) <= _myWizard.Radius + _myGame.BonusRadius)

                &&

                (tickT % BONUS_RESPAWN_INTERVAL < BONUS_RESPAWN_INTERVAL - BONUS_PRERESPAWN_INTERVAL && tickT % BONUS_RESPAWN_INTERVAL > 5)

                &&

                GetClosestBonus() != null && GetClosestBonus().GetDistanceTo(_myWizard) > bonusPeekDistance

                ||

                 ((tickT % BONUS_RESPAWN_INTERVAL > 5 && tickT % BONUS_RESPAWN_INTERVAL < BONUS_RESPAWN_INTERVAL - BONUS_PRERESPAWN_INTERVAL) && GetClosestBonus() == null))

                /*!_myWorld.Bonuses.Any()*/)
            {
                prevState = StateType.Idling;
                state = StateType.Walk;
            }

            if (state == StateType.GetBonus)
            {

                //идем к ближайшей позиции с бонусом и встаем рядом, ждем
                var closestBonus = bonusPositions[0].GetDistanceTo(_myWizard) <=
                                   bonusPositions[1].GetDistanceTo(_myWizard)
                    ? bonusPositions[0]
                    : bonusPositions[1];

                if (_myWizard.GetDistanceTo(closestBonus.GetX(), closestBonus.GetY()) > _myWizard.Radius + _myGame.BonusRadius + MapRadar.K)
                {
                    goToPosition = closestBonus;
                    noTurnWhileWalking = false;
                    //GoTo(closestBonus);
                }

                //если бонус появился, идем туда
                if (_myWorld.Bonuses.Any())
                {
                    var minDistance = double.MaxValue;
                    var myClosestBonus = (Bonus)null;
                    foreach (var bonus in _myWorld.Bonuses)
                    {
                        var distance = bonus.GetDistanceTo(_myWizard);
                        if (distance < minDistance)
                        {
                            minDistance = distance;
                            myClosestBonus = bonus;
                        }
                    }

                    if (myClosestBonus != null)
                    {
                        goToPosition = new Point2D(myClosestBonus.X, myClosestBonus.Y);
                        noTurnWhileWalking = false;
                        //GoTo(new Point2D(myClosestBonus.X, myClosestBonus.Y));
                    }
                }
            }

            //if (state == StateType.Pursuit)
            //{
            //    if (pursuitPoint != null)
            //    {
            //        GoTo(new Point2D(pursuitPoint.GetX(), pursuitPoint.GetY()));
            //    }
            //    if (pursuitTarget != null)
            //    {
            //        GoTo(new Point2D(pursuitTarget.X, pursuitTarget.Y));
            //    }

            //    if (_myWizard.Skills.Any(i => i == SkillType.Haste) && _myWizard.Statuses.All(i => i.Type != StatusType.Hastened))
            //    {
            //        _myMove.Action = ActionType.Haste;
            //    }
            //}

            if (state == StateType.Walk && myPositionsBeforeBonusState != null)
            {
                goToPosition = myPositionsBeforeBonusState;
                noTurnWhileWalking = false;
                //GoTo(myPositionsBeforeBonusState);
            }


            var enemyCreeps = GetNearestAttackableTargets();
            if (enemyCreeps.Any(i => _myWizard.GetDistanceTo(i.X, i.Y) < SAFE_DISTANCE/*_myGame.StaffRange+i.Radius*/))
            {
                state = StateType.Retreat;
            }

            //отходим, если хотя бы один вражеcкий маг может по нам попасть
            var visibleEnemyWizards = GetNearestVisibleTargets(UnitType.Wizard).OfType<Wizard>().Where(i => i != null).ToList();
            if (_myWizard.Life<HIGH_HP_FACTOR && state != StateType.Retreat && visibleEnemyWizards.Any(i => _myWizard.GetDistanceTo(i) <= i.CastRange+_myWizard.Radius))
            {
                foreach (var visibleEnemyWizard in visibleEnemyWizards)
                {
                    var wizardMagicMissleCooldown =
                        visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.MagicMissile];

                    var wizardFrostBoltCooldown = visibleEnemyWizard.Skills.Any(i=>i == SkillType.FrostBolt) ? 
                        visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.FrostBolt] : int.MaxValue;

                    var wizardFireballCooldown = visibleEnemyWizard.Skills.Any(i => i == SkillType.Fireball) ?
                      visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.Fireball] : int.MaxValue;

                    var cooldowns = new []
                        {wizardMagicMissleCooldown, wizardFrostBoltCooldown, wizardFireballCooldown};

                    var wizardCooldown = cooldowns.Min();

                    var wizardAngleToMe = visibleEnemyWizard.GetAngleTo(_myWizard);
                    var turningSpeed = _myGame.WizardMaxTurnAngle;

                    var enemyTicksToTurn = Math.Floor(Math.Abs(wizardAngleToMe / turningSpeed));
                    //var myTicksToTurn = Math.Floor(Math.Abs(_myWizard.GetAngleTo(visibleEnemyWizard) / turningSpeed));

                    var ticksToTurn = enemyTicksToTurn;// < myTicksToTurn ? enemyTicksToTurn: myTicksToTurn;

                    var myTicksToRetreat = wizardCooldown > ticksToTurn ? wizardCooldown : ticksToTurn;
                    var distanceToRetreat = visibleEnemyWizard.CastRange + _myWizard.Radius - _myWizard.GetDistanceTo(visibleEnemyWizard);

                    var currentTicksToRetreat = Math.Ceiling(distanceToRetreat / _myGame.WizardStrafeSpeed);

                    if (!(state==StateType.GetBonus && _myWizard.Life>=HIGH_HP_FACTOR)  && myTicksToRetreat <= currentTicksToRetreat)
                    {
                        state = StateType.Retreat;
                        break;
                    }
                }
            }

            //отходим, если хотя бы один вражекий фетиш может по нам попасть
            var visibleEnemyMinions = GetNearestVisibleTargets(UnitType.Minion).OfType<Minion>().Where(i => i.Type==MinionType.FetishBlowdart).ToList();
            if (state != StateType.GetBonus && state != StateType.Retreat && visibleEnemyMinions.Any(i => _myWizard.GetDistanceTo(i) <= _myGame.FetishBlowdartAttackRange+_myWizard.Radius+i.Radius))
            {
                state = StateType.Retreat;
            }




            var target = GetTarget();
            LivingUnit pursuitTarget=null;

            if (target!=null && target is Minion && state!=StateType.Retreat && state!=StateType.GetBonus)
            {
                pursuitTarget = GetPuruitTarget();
            }

            if (state == StateType.Retreat)
            {
                var noTurningForward = target != null;
                goToPosition = GetPreviousWaypoint();
                noTurnWhileWalking = noTurningForward;
                //GoTo(GetPreviousWaypoint(), noTurningForward);
            }

            if (target != null)
            {
                var angleToTarget = _myWizard.GetAngleTo(target);
                var turningSpeed = _myGame.WizardMaxTurnAngle;
                var ticksToTurn = Math.Floor(Math.Abs(angleToTarget / turningSpeed));

                var magicMissleCooldown = _myWizard.RemainingCooldownTicksByAction[(int)ActionType.MagicMissile];

                //var canAttackTarget = CanAttackTarget(target);

                if (state != StateType.Retreat && state != StateType.GetBonus)
                {
                    state = StateType.Attack;
                }

                if (magicMissleCooldown > ticksToTurn 
                    &&
                     _myWizard.GetDistanceTo(target) > SAFE_DISTANCE)
                {

                    var nearestEnemyWizard = GetNearestTarget(UnitType.Wizard);
                    if (nearestEnemyWizard != null)
                    {
                        var angleToWizard = _myWizard.GetAngleTo(nearestEnemyWizard);
                        var newAngle = angleToWizard > 0 ? angleToWizard - Math.PI / 2 : angleToWizard + Math.PI / 2;
                        _myMove.Turn = newAngle;

                        
                    }

                }
                else
                {
                    Attack(target);
                }

                if (pursuitTarget!=null)
                {

                    if (state != StateType.Retreat && state != StateType.GetBonus)
                    {
                        state = StateType.Pursuit;
                    }

                    goToPosition = new Point2D(target.X, target.Y);
                    noTurnWhileWalking = false;
                    //GoTo(new Point2D(target.X, target.Y), true);
                }

            }

            if (state == StateType.Idling)
            {
                goToPosition = GetNextWaypoint();
                noTurnWhileWalking = false;
                //GoTo(GetNextWaypoint());
            }

            //for experimental NEO system
            var projectiles =
                _myWorld.Projectiles.ToList();
            if (projectiles.Any())
            {
                projectiles = projectiles.Where(
                    i => i.Faction != _myWizard.Faction && i.OwnerPlayerId != -1 && i.GetDistanceTo(_myWizard) <= _myWizard.VisionRange).ToList();
            }

            if (state != StateType.Retreat && projectiles.Any())
            {
                foreach (var projectile in projectiles)
                {

                    //получаем коэффициенты прямой движения снаряда
                    var x1 = projectile.X;
                    var x2 = projectile.X + (Math.Abs(projectile.SpeedX) > 0.000001D ? projectile.SpeedX : 0.00001D); //??????????
                    var y1 = projectile.Y;
                    var y2 = projectile.Y + projectile.SpeedY;

                    

                    var xC = _myWizard.X;
                    var yC = _myWizard.Y;

                    var r = _myWizard.Radius + projectile.Radius;
                    
                    
                    var k = (y2 - y1) / (x2 - x1); //угловой Коэффицент прямой
                    var b = (x2 * y1 - x1 * y2) / (x2 - x1); //смещение прямой

                    //var b = -((y2 - y1)/(x2 - x1)*x1 - y1);

                    //подставляем координату по Х, смотрим, попадает ли координата У в волшебника
                    var x = _myWizard.X;
                    var y = k * x + b;

                    // x2+y2<=R+Rp

                    //если снаряд летит в нашу сторону
                    if (IsLineIntercectCircle(x1, y1, x2, y2, xC, yC, r))
                    {

                        //проверим, попадет ли снаряд в кого-то другого
                        var allyForces=new List<LivingUnit>();

                        //миньоны
                        allyForces.AddRange(
                            _myWorld.Minions.Where(
                                i =>
                                    i.Faction == _myWizard.Faction &&
                                    _myWizard.GetDistanceTo(i) <= _myWizard.GetDistanceTo(projectile)).ToList());

                        //волшебники
                        allyForces.AddRange(_myWorld.Wizards.Where(
                                i =>
                                    i.Faction == _myWizard.Faction && !i.IsMe
                                    &&
                                    _myWizard.GetDistanceTo(i) <= _myWizard.GetDistanceTo(projectile)));

                        //здания
                        allyForces.AddRange(_myWorld.Buildings.Where(
                              i =>
                                  i.Faction == _myWizard.Faction &&
                                  _myWizard.GetDistanceTo(i) <= _myWizard.GetDistanceTo(projectile)));

                        var projectileIntercectAlly = false;
                        if (allyForces.Any())
                        {
                            foreach (var unit in allyForces)
                            {
                                if (IsLineIntercectCircle(x1, y1, x2, y2, unit.X, unit.Y, unit.Radius + projectile.Radius) && _myWizard.GetDistanceTo(projectile)>unit.GetDistanceTo(projectile))
                                {
                                    projectileIntercectAlly = true;
                                    break;
                                }
                            }
                        }

                        if (!projectileIntercectAlly)
                        {

                            var angleToProjectile = _myWizard.GetAngleTo(projectile);
                            var newK = (-1/k);
                            var newAngle = Math.Atan(newK);
                            var l = angleToProjectile > 0 ? -200 : 200;

                            var newX = _myWizard.X + l*Math.Cos(newAngle);
                            var newY = newK*(newX - _myWizard.X) + _myWizard.Y;

                            GlobalPath = new List<Point2D>();
                            if (state != StateType.GetBonus)
                            {
                                state = StateType.Neo;
                            }
                            goToPosition = new Point2D(newX, newY);
                            noTurnWhileWalking = false;
                            //GoTo(new Point2D(newX, newY));
                        }
                    }

                }
            }

            if (state != StateType.Attack && (!(target is Tree)) && _myWizardPrev != null && Math.Abs(_myWizard.X - _myWizardPrev.X) < MapRadar.K &&
              Math.Abs(_myWizard.Y - _myWizardPrev.Y) < MapRadar.K)
            {
                var closestTree = GetNearestTarget(UnitType.Tree);
                if (closestTree != null &&
                    closestTree.GetDistanceTo(_myWizard) <= _myWizard.Radius*2 + closestTree.Radius + 5)
                {
                    GlobalPath = new List<Point2D>();
                    if (state != StateType.GetBonus)
                    {
                        state = StateType.Attack;
                     }
                    target = closestTree;
                    Attack(target);
                    noTurnWhileWalking = true;
                    _myMove.Turn = _myWizard.GetAngleTo(closestTree.X, closestTree.Y);
                }

            }

            if (_myWizard.Skills.Any(i => i == SkillType.Haste) && _myWizard.Statuses.All(i => i.Type != StatusType.Hastened))
            {
                _myMove.Action = ActionType.Haste;
            }
            if ( _myWizard.Skills.Any(i => i == SkillType.Shield) && _myWizard.Statuses.All(i => i.Type != StatusType.Shielded))
            {
                _myMove.Action = ActionType.Shield;
            }

            if (state != StateType.Attack && treeListToDestroy.Any())
            {
                var closestTreeToDestoy = treeListToDestroy.OrderBy(i => _myWizard.GetDistanceTo(i)).FirstOrDefault();
                if (closestTreeToDestoy != null && _myWizard.GetDistanceTo(closestTreeToDestoy) <= _myWizard.CastRange+closestTreeToDestoy.Radius)
                {
                    Attack(closestTreeToDestoy);
                }
            }

            if (laneSwitchPoint != null)
            {
                if (_myWizard.GetDistanceTo(laneSwitchPoint.GetX(), laneSwitchPoint.GetY()) <= _myWizard.VisionRange / 2)
                {
                    laneSwitchPoint = null;
                    myPositionsBeforeBonusState = null;
                    goToPosition = GetNextWaypoint();
                }
                else
                {
                    state = StateType.Walk;
                    goToPosition = laneSwitchPoint;
                    noTurnWhileWalking = target!=null;
                    //GoTo(laneSwitchPoint);
                }

            }

            if (goToPosition != null)
            {
                GoTo(goToPosition, noTurnWhileWalking);
            }

            Console.WriteLine(state);

            return;

        }


        public bool CanAttackTarget(LivingUnit unit)
        {
            var distanceToTarget = _myWizard.GetDistanceTo(unit);
            return distanceToTarget <= _myWizard.CastRange+_myWizard.Radius;
        }

        public bool CanPursuitTarget(LivingUnit unit)
        {

            if (state == StateType.Retreat || state == StateType.GetBonus)
            {
                return false;
            }

            if (_myWizard.GetDistanceTo(unit) < _myWizard.CastRange)
            {
                return false;
            }

            return true;
        }

        public LivingUnit GetPuruitTarget()
        {

            //если есть кто-то ближе, чем минимальная дистанция, то у нас нет цели преследования
            var closestTarget = GetNearestTarget();
            if (closestTarget != null && _myWizard.GetDistanceTo(closestTarget) <= SAFE_DISTANCE)
            {
                return null;
            }

            //здания за пределами cast range
            var attackableBuildings = GetNearestVisibleTargets(UnitType.Building);
            if (attackableBuildings.Any(i=>_myWizard.GetDistanceTo(i)>_myWizard.CastRange+i.Radius))
            {
                var result = attackableBuildings.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }

            //волшебники за пределами cast range, до которых мы добежим до их перезарядки
            var attackableEnemyWizards = new List<LivingUnit>();

            var visibleEnemyWizards = GetNearestVisibleTargets(UnitType.Wizard).OfType<Wizard>().Where(i => i != null && _myWizard.GetDistanceTo(i)>_myWizard.CastRange+i.Radius).ToList();
            foreach (var visibleEnemyWizard in visibleEnemyWizards)
            {
                var wizardMagicMissleCooldown =
                    visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.MagicMissile];

                var wizardFrostBoltCooldown = visibleEnemyWizard.Skills.Any(i => i == SkillType.FrostBolt) ?
                    visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.FrostBolt] : int.MaxValue;

                var wizardFireballCooldown = visibleEnemyWizard.Skills.Any(i => i == SkillType.Fireball) ?
                  visibleEnemyWizard.RemainingCooldownTicksByAction[(int)ActionType.Fireball] : int.MaxValue;

                var cooldowns = new[]
                    {wizardMagicMissleCooldown, wizardFrostBoltCooldown, wizardFireballCooldown};

                var wizardCooldown = cooldowns.Min();

                var wizardAngleToMe = visibleEnemyWizard.GetAngleTo(_myWizard);
                var turningSpeed = _myGame.WizardMaxTurnAngle;

                var enemyTicksToTurn = Math.Floor(Math.Abs(wizardAngleToMe / turningSpeed));
                var myTicksToTurn = Math.Floor(Math.Abs(_myWizard.GetAngleTo(visibleEnemyWizard) / turningSpeed));

                var ticksToTurn = enemyTicksToTurn < myTicksToTurn ? enemyTicksToTurn : myTicksToTurn;

                var wizardTickToAttack = wizardCooldown > ticksToTurn ? wizardCooldown : ticksToTurn;

                var tickToPursuit = Math.Floor(_myWizard.GetDistanceTo(visibleEnemyWizard) - (_myWizard.CastRange + visibleEnemyWizard.Radius)) /
                                    _myGame.WizardStrafeSpeed;

                if (tickToPursuit > wizardTickToAttack)
                {
                    wizardTickToAttack = tickToPursuit;
                }

                var distanceToPursuit = _myWizard.GetDistanceTo(visibleEnemyWizard) -
                                        (_myWizard.CastRange + visibleEnemyWizard.Radius); //visibleEnemyWizard.CastRange - _myWizard.GetDistanceTo(visibleEnemyWizard) + MapRadar.K;
                if (distanceToPursuit < 0)
                {
                    distanceToPursuit = 0;
                }

                var currentTicksToPursuit = Math.Ceiling(distanceToPursuit / _myGame.WizardStrafeSpeed);

                if (wizardTickToAttack > currentTicksToPursuit)
                {
                    attackableEnemyWizards.Add(visibleEnemyWizard);
                }
            }
            if (attackableEnemyWizards.Any())
            {
                var result = attackableEnemyWizards.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }


            //фетиши за пределами cast range
            var attackableFetishes =
               GetNearestVisibleTargets(UnitType.Minion)
                   .OfType<Minion>()
                   .Where(i => i.Type == MinionType.FetishBlowdart && _myWizard.GetDistanceTo(i)>_myWizard.CastRange+i.Radius).ToList();
            if (attackableFetishes.Any())
            {
                var result = attackableFetishes.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }

            return null;

        }

        public LivingUnit GetTarget()
        {

            //var enemyWizards = GetNearestVisibleTargets(UnitType.Wizard);
            //var enemyBuildings = GetNearestVisibleTargets(UnitType.Building);
            //var enemyMinions = GetNearestVisibleTargets(UnitType.Minion);

            var closestTarget = GetNearestTarget();
            if (closestTarget != null && _myWizard.GetDistanceTo(closestTarget) <= SAFE_DISTANCE)
            {
                return closestTarget;
            }


            var attackableBuildings = GetNearestAttackableTargets(UnitType.Building);
            if (attackableBuildings.Any())
            {
                var result = attackableBuildings.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }

            if (_myWizard.RemainingCooldownTicksByAction[(int)ActionType.MagicMissile] == 0)
            {
                var weekestMinion = GetNearestAttackableTargets(UnitType.Minion).Where(i => i.Life <= _myGame.MagicMissileDirectDamage).OrderBy(i => _myWizard.GetDistanceTo(i)).FirstOrDefault();
                if (weekestMinion != null)
                {
                    return weekestMinion;
                }
            }

            var attackableWizards = GetNearestAttackableTargets(UnitType.Wizard);
            if (attackableWizards.Any())
            {
                var result = attackableWizards.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }


            var attackableFetishes =
                GetNearestAttackableTargets(UnitType.Minion)
                    .OfType<Minion>()
                    .Where(i => i.Type == MinionType.FetishBlowdart).ToList();
            if (attackableFetishes.Any())
            {
                var result = attackableFetishes.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }


            var attackableMinions = GetNearestAttackableTargets(UnitType.Minion);
            if (attackableMinions.Any())
            {
                var result = attackableMinions.OrderBy(i => i.Life).FirstOrDefault();
                return result;
            }
           

            return null;
        }

        public bool Attack(LivingUnit target)
        {

            //if (_myMove.Action != null)
            //{
            //    return true;
            //}



            var distance = _myWizard.GetDistanceTo(target);
            var tickToHit = Math.Ceiling(_myGame.MagicMissileSpeed/distance);

            var targetPositionDeltaX = target.SpeedX*tickToHit;
            var targetPositionDeltaY = target.SpeedX * tickToHit;

            var hitPoint = new Point2D(target.X+targetPositionDeltaX, target.Y+targetPositionDeltaY);

            var angle = _myWizard.GetAngleTo(hitPoint.GetX(), hitPoint.GetY());

            _myMove.Turn = angle;

            // Если цель перед нами, ...
            if (Math.Abs(angle) < _myGame.StaffSector / 2.0D)
            {
                // ... то атакуем.
                _myMove.Action = ActionType.MagicMissile;
                if (((!GetNearestVisibleTargets(UnitType.Wizard).Any() && _myWizard.Mana >= _myWizard.MaxMana * 0.5) ||
                     target is Wizard || target.GetDistanceTo(_myWizard) <= _myGame.WizardCastRange / 3) &&
                    _myWizard.Skills.Any(i => i == SkillType.FrostBolt) &&
                    target.Statuses.All(i => i.Type != StatusType.Frozen) && _myWizard.RemainingCooldownTicksByAction[(int)ActionType.FrostBolt]==0)
                {
                    _myMove.Action = ActionType.FrostBolt;
                }

                if (_myWizard.GetDistanceTo(hitPoint.GetX(), hitPoint.GetY()) > _myGame.FireballExplosionMinDamageRange +target.Radius+_myWizard.Radius
                    &&
                    (target is Wizard || target is Building || _myWizard.Mana >= _myWizard.MaxMana*0.5)
                    && 
                    _myWizard.RemainingCooldownTicksByAction[(int) ActionType.Fireball] == 0
                    && 
                    _myWizard.Skills.Any(i => i == SkillType.Fireball) 
                    &&
                    target.Statuses.All(i => i.Type != StatusType.Burning)
                    &&
                    _myWizard.RemainingCooldownTicksByAction[(int)ActionType.Fireball] == 0)
                {
                    _myMove.Action = ActionType.Fireball;
                }
               
                if (distance <= _myGame.StaffRange+target.Radius)
                {
                    _myMove.Action = ActionType.Staff;
                }

                if (_myWizard.Skills.Any(i => i == SkillType.Haste) && _myWizard.Statuses.All(i => i.Type != StatusType.Hastened) 
                    && (!_myWizard.Skills.Any(i => i == SkillType.Fireball) || _myWizard.Skills.Any(i => i == SkillType.Fireball) && _myWizard.RemainingCooldownTicksByAction[(int)ActionType.Fireball]>_myWizard.RemainingActionCooldownTicks))
                {
                    _myMove.Action = ActionType.Haste;
                }

                _myMove.CastAngle = angle;
                _myMove.MinCastDistance = (distance - target.Radius + _myGame.MagicMissileRadius);

            }
           



            return true;
        }

        public Point2D[] GetWaypointsByLaneType(LaneType laneType)
        {
            double mapSize = 4000;
            var result = new List<Point2D>();
            switch (laneType)
            {
                    case LaneType.Top:
                        result = new List<Point2D>
                        {
                            new Point2D(100.0D, mapSize - 100.0D),
                            new Point2D(100.0D, mapSize - 400.0D),
                            new Point2D(200.0D, mapSize - 800.0D),
                            new Point2D(200.0D, mapSize*0.75D),
                            new Point2D(200.0D, mapSize*0.5D),
                            new Point2D(200.0D, mapSize*0.25D),
                            new Point2D(200.0D, 200.0D),
                            new Point2D(mapSize*0.25D, 200.0D),
                            new Point2D(mapSize*0.5D, 200.0D),
                            new Point2D(mapSize*0.75D, 200.0D),
                            new Point2D(mapSize - 200.0D, 200.0D)
                        };
                    break;
                case LaneType.Middle:
                    result = new List<Point2D>
                    {
                         new Point2D(100.0D, mapSize - 100.0D),
                        new Point2D(200.0D, mapSize - 600.0D),
                        new Point2D(500D, mapSize - 700.0D),//
                        new Point2D(800.0D, mapSize - 800.0D),
                        new Point2D(mapSize*0.5D, mapSize*0.5D),
                        new Point2D(mapSize - 800.0D, 800.0D),
                        new Point2D(mapSize - 700.0D, 500D),//
                        new Point2D(mapSize - 600.0D, 600.0D)
                    };
                    break;
                case LaneType.Bottom:
                    result = new List<Point2D>
                    {
                        new Point2D(100.0D, mapSize - 100.0D),
                        new Point2D(400.0D, mapSize - 100.0D),
                        new Point2D(800.0D, mapSize - 200.0D),
                        new Point2D(mapSize*0.25D, mapSize - 200.0D),
                        new Point2D(mapSize*0.5D, mapSize - 200.0D),
                        new Point2D(mapSize*0.75D, mapSize - 200.0D),
                        new Point2D(mapSize - 200.0D, mapSize - 200.0D),
                        new Point2D(mapSize - 200.0D, mapSize*0.75D),
                        new Point2D(mapSize - 200.0D, mapSize*0.5D),
                        new Point2D(mapSize - 200.0D, mapSize*0.25D),
                        new Point2D(mapSize - 200.0D, 200.0D)
                    };
                    break;
            }

            return result.ToArray();
        }

        void InitializeStrategy(Wizard self, Game game)
        {
            //if (random == null)
            //{
            //  random = new Random(game.RandomSeed);

            if (StartPosition == null)
            {
                StartPosition = new Point2D(self.X, self.Y);
            }

            double mapSize = game.MapSize;

            switch ((int)self.Id)
            {
                //case 1:
                //case 2:
                //case 6:
                //case 7:
                //    lane = LaneType.Top;
                //    waypoints =GetWaypointsByLaneType(lane);
                //    break;
                //case 3:
                //case 8:
                //    lane = LaneType.Middle;
                //    waypoints = GetWaypointsByLaneType(lane);
                //    break;
                //case 4:
                //case 5:
                //case 9:
                //case 10:
                //    lane = LaneType.Bottom;
                //    waypoints = GetWaypointsByLaneType(lane);
                //    break;

        }


            lane = LaneType.Middle;
            waypoints = GetWaypointsByLaneType(lane);

        }

        /**
         * Сохраняем все входные данные в полях класса для упрощения доступа к ним.
         */

        private void InitializeTick(Wizard self, World world, Game game, Move move)
        {
            if (_myWizard != null && _myWorld != null && _myGame != null && _myMove != null)
            {
                _myWizardPrev = _myWizard;
                _myWorldPrev = _myWorld;
                _myGamePrev = _myGame;
                _myMovePrev = _myMove;
            }

            _myWizard = self;
            _myWorld = world;
            _myGame = game;
            _myMove = move;
        }

        /**
         * Данный метод предполагает, что все ключевые точки на линии упорядочены по уменьшению дистанции до последней
         * ключевой точки. Перебирая их по порядку, находим первую попавшуюся точку, которая находится ближе к последней
         * точке на линии, чем волшебник. Это и будет следующей ключевой точкой.
         * <p>
         * Дополнительно проверяем, не находится ли волшебник достаточно близко к какой-либо из ключевых точек. Если это
         * так, то мы сразу возвращаем следующую ключевую точку.
         */

        private Point2D GetNextWaypoint()
        {

            int lastWaypointIndex = waypoints.Length - 1;
            Point2D lastWaypoint = waypoints[lastWaypointIndex];

            for (int waypointIndex = 0; waypointIndex < lastWaypointIndex; ++waypointIndex)
            {
                Point2D waypoint = waypoints[waypointIndex];

                if (waypoint.GetDistanceTo(_myWizard) <= WAYPOINT_RADIUS)
                {
                    return waypoints[waypointIndex + 1];
                }

                if (lastWaypoint.GetDistanceTo(waypoint) < lastWaypoint.GetDistanceTo(_myWizard))
                {
                    return waypoint;
                }
            }

            return lastWaypoint;
        }

        /**
         * Действие данного метода абсолютно идентично действию метода {@code getNextWaypoint}, если перевернуть массив
         * {@code waypoints}.
         */

        private Point2D GetPreviousWaypoint()
        {

            //test

            Point2D firstWaypoint = waypoints[0];

            for (int waypointIndex = waypoints.Length - 1; waypointIndex > 0; --waypointIndex)
            {
                Point2D waypoint = waypoints[waypointIndex];

                if (waypoint.GetDistanceTo(_myWizard) <= WAYPOINT_RADIUS)
                {
                    return waypoints[waypointIndex - 1];
                }

                if (firstWaypoint.GetDistanceTo(waypoint) < firstWaypoint.GetDistanceTo(_myWizard))
                {
                    return waypoint;
                }
            }

            return firstWaypoint;
        }

        /**
         * Простейший способ перемещения волшебника.
         */
        //уже - нет

        private static Point2D cachedPointToGo;

        private void GoTo(Point2D point, bool noTurn = false)
        {

            if (point.GetDistanceTo(_myWizard) <= _myWizard.Radius * 1.2)
            {
                if (prevState == StateType.Walk)
                {
                    state = StateType.Idling;
                }
                return;
            }

            var pointToGo = point;

            //if (GlobalPath == null || GlobalPath.Count < 1)
            //{
            //    shouldUseGlobalPath = false;
            //}
            //if (!(state == StateType.Attack && prevState == StateType.Pursuit || state == StateType.Pursuit && prevState == StateType.Attack) && _myWizardPrev != null
            //    && Math.Abs(_myWizard.X - _myWizardPrev.X) < 1 && Math.Abs(_myWizard.Y - _myWizardPrev.Y) < 1)
            //{
            //    //Console.WriteLine("switch to A*");
            //    shouldUseGlobalPath = true;
            //    GlobalPath = new List<Point2D>();

            //}

            shouldUseGlobalPath = state!= StateType.Neo;

            if (shouldUseGlobalPath)
            {
                if (cachedPointToGo == null)
                {
                    cachedPointToGo = point;
                }
                if (Math.Abs(point.GetX() - cachedPointToGo.GetX()) > 20 ||
                    Math.Abs(point.GetY() - cachedPointToGo.GetY()) > 20)
                {
                    GlobalPath = new List<Point2D>();
                    cachedPointToGo = new Point2D(point.GetX(), point.GetY());
                    //shouldUseGlobalPath = false;
                }

            }

            //////
          
            if (shouldUseGlobalPath)
            {


                if (prevState != state)
                {
                    if (prevState == StateType.Attack && state == StateType.Pursuit ||
                        prevState == StateType.Pursuit && state == StateType.Attack)
                    {

                    }
                    else
                    {
                        GlobalPath = new List<Point2D>();
                        //Console.WriteLine("Change PATH");
                    }
                }

                pointToGo = new Point2D(point.GetX(), point.GetY());

                if (shouldUseGlobalPath && (GlobalPath == null || GlobalPath.Count == 0))
                {
                    var myCoord = new Point2D(_myWizard.X, _myWizard.Y);
                    GlobalPath = new List<Point2D>();

                    MapRadar.MapHeight = _myGame.MapSize;
                    MapRadar.MapWidth = _myGame.MapSize;
                    MapRadar.MeRadius = _myWizard.Radius;
                    MapRadar.WizardViewDistance = _myWizard.VisionRange;

                    var path = MapRadar.FindPath(myCoord, point);
                    if (path != null && path.Any())
                    {
                        GlobalPath.AddRange(path);
                        if (path[path.Count - 1].GetDistanceTo(point) <= MapRadar.PointDelta)
                        {
                            GlobalPath.Add(point);
                        }
                    }
                }

                if (GlobalPath != null && GlobalPath.Any())
                {
                    var firstPoint = GlobalPath[0];

                    if (Math.Abs(firstPoint.GetX() - _myWizard.X) < MapRadar.K &&
                        Math.Abs(firstPoint.GetY() - _myWizard.Y) < MapRadar.K)
                    {
                        GlobalPath.RemoveAt(0);
                    }



                    if (GlobalPath.Count > 0)
                    {
                        pointToGo = GlobalPath[0];
                    }

                }
            }

            var angle = _myWizard.GetAngleTo(pointToGo.GetX(), pointToGo.GetY());

            Console.WriteLine($"Walking to X:{pointToGo.GetX()}, Y:{pointToGo.GetY()}");

            if (!noTurn)
            {
                _myMove.Turn = angle;
            }

            var isMovingForward = angle > -Math.PI / 2 && angle < Math.PI / 2;
            var xSpeed = Math.Cos(angle);
            var ySpeed = Math.Sin(angle);

            if (Math.Abs(xSpeed) > Math.Abs(ySpeed))
            {
                xSpeed = xSpeed / Math.Abs(xSpeed);
                ySpeed = ySpeed / Math.Abs(xSpeed);
            }
            else
            {
                xSpeed = xSpeed / Math.Abs(ySpeed);
                ySpeed = ySpeed / Math.Abs(ySpeed);
            }

            //???
            double scaling;

            var speedBonus = GetSpeedBonusFactor();



            if (!isMovingForward)
            {
                scaling = _myGame.WizardBackwardSpeed * speedBonus;
            }
            else if (ySpeed > xSpeed)
            {
                scaling = _myGame.WizardBackwardSpeed * speedBonus;
            }
            else
            {
                scaling = _myGame.WizardForwardSpeed * speedBonus;
            }

            xSpeed *= scaling;
            ySpeed *= scaling;

            if (Math.Abs(ySpeed) > _myGame.WizardStrafeSpeed * (1 + speedBonus))
            {
                xSpeed = xSpeed / Math.Abs(ySpeed) * _myGame.WizardStrafeSpeed * (1 + speedBonus);
                ySpeed = ySpeed / Math.Abs(ySpeed) * _myGame.WizardStrafeSpeed * (1 + speedBonus);
            }

            var distanceToPoint = _myWizard.GetDistanceTo(pointToGo.GetX(), pointToGo.GetY());
            var deltaDistance = Math.Sqrt(xSpeed * xSpeed + ySpeed * ySpeed);

            if (deltaDistance > distanceToPoint)
            {
                xSpeed = Math.Cos(angle) * deltaDistance;
                ySpeed = Math.Sin(angle) * deltaDistance;
            }

            _myMove.Speed = xSpeed;
            _myMove.StrafeSpeed = ySpeed;

        }

        private double GetStrafeSpeed(double angle)
        {

            double atg = Math.Tan(angle);
            return 12 * Math.Sin(angle) * Math.Sqrt((atg * atg + 1) / (9 + 16 * atg * atg));
        }

        private double GetSpeed(double angle)
        {
            double atg = Math.Tan(angle);
            return 12 * Math.Cos(angle) * Math.Sqrt((atg * atg + 1) / (9 + 16 * atg * atg));
        }

        public double GetSpeedBonusFactor()
        {
            var speedBonus = 0D;

            speedBonus+= _myWizard.Statuses.Any(i => i.Type == StatusType.Hastened)
               ? _myGame.HastenedMovementBonusFactor
               : 0;

            if (_myWizard.Skills.Any(i => i == SkillType.MovementBonusFactorPassive1))
            {
                speedBonus += _myGame.MovementBonusFactorPerSkillLevel;
            }
            if (_myWizard.Skills.Any(i => i == SkillType.MovementBonusFactorAura1))
            {
                speedBonus += _myGame.MovementBonusFactorPerSkillLevel;
            }
            if (_myWizard.Skills.Any(i => i == SkillType.MovementBonusFactorPassive2))
            {
                speedBonus += _myGame.MovementBonusFactorPerSkillLevel;
            }
            if (_myWizard.Skills.Any(i => i == SkillType.MovementBonusFactorAura2))
            {
                speedBonus += _myGame.MovementBonusFactorPerSkillLevel;
            }

            return 1D + speedBonus;
        }

        public void UpdateTreeListToDestroy()
        {
            if (treeListToDestroy.Any())
            {
                var copiedList = new List<Tree>(treeListToDestroy);
                foreach (var tree in copiedList)
                {
                    if (!_myWorld.Trees.Any(i => Math.Abs(i.X - tree.X) < 1 && Math.Abs(i.Y - tree.Y) < 1))
                    {
                        treeListToDestroy.Remove(tree);
                    }
                }
            }
        }

        public void UpdateTowerCooldown(int byValue)
        {
            foreach (var cooldown in TowersGlobalCooldown.Where(i=>i.Value!=-1).ToList())
            {
                var allyForces = new List<LivingUnit>();
                allyForces.AddRange(_myWorld.Wizards.Where(i=>i.Faction==_myWizard.Faction));
                allyForces.AddRange(_myWorld.Minions.Where(i=>i.Faction==_myWizard.Faction));

                var towerWasDestoyed = false;
                foreach (var ally in allyForces)
                {
                    var visionRange = 0D;
                    var minion = ally as Minion;
                    if (minion != null)
                    {
                        visionRange = minion.VisionRange;
                    }
                    else
                    {
                        var wizard = ally as Wizard;
                        if (wizard != null)
                        {
                            visionRange = wizard.VisionRange;
                        }
                    }

                    if (ally.GetDistanceTo(cooldown.Key.GetX(), cooldown.Key.GetY()) <= visionRange &&
                        !_myWorld.Buildings.Any(i => i.GetDistanceTo(ally) <= visionRange))
                    {
                        towerWasDestoyed = true;
                    }
                }
               

                if (towerWasDestoyed)
                {
                    TowersGlobalCooldown[cooldown.Key] = -1;
                }
                else
                {

                    var closestTower =
                        _myWorld.Buildings.FirstOrDefault(
                            i =>
                                i.Faction != _myWizard.Faction && i.Type == BuildingType.GuardianTower &&
                                Math.Abs(i.X - cooldown.Key.GetX()) <= 1 && Math.Abs(i.Y - cooldown.Key.GetY()) <= 1);
                    if (closestTower != null)
                    {
                        TowersGlobalCooldown[cooldown.Key] = closestTower.RemainingActionCooldownTicks;
                    }
                    else
                    {
                        if (cooldown.Value > 0)
                        {
                            TowersGlobalCooldown[cooldown.Key] -= byValue;
                        }
                    }
                }
            }
        }

        //public double



        public enum StateType
        {
            Idling,
            Walk,
            Pursuit,
            Retreat,
            Attack,
            GetBonus,
            Neo
        }

        public enum UnitType
        {
            All,
            Building,
            Wizard,
            Minion,
            Tree,
            Bonus
        }

        private Bonus GetClosestBonus()
        {

            if (!_myWorld.Bonuses.Any())
            {
                return null;
            }

            Bonus nearestBonus = null;
            double nearestBonusDistance = double.MaxValue;

            foreach (var bonus in _myWorld.Bonuses)
            {
                double distance = _myWizard.GetDistanceTo(bonus);

                if (distance < nearestBonusDistance)
                {
                    nearestBonus = bonus;
                    nearestBonusDistance = distance;
                }
            }

            return nearestBonus;
        }

        private LivingUnit GetNearestTarget(UnitType type = UnitType.All)
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            switch (type)
            {
                case UnitType.All:
                    targets.AddRange(_myWorld.Buildings);
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    targets.AddRange(_myWorld.Minions);
                    break;
                case UnitType.Building:
                    targets.AddRange(_myWorld.Buildings);
                    break;
                case UnitType.Wizard:
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    break;
                case UnitType.Minion:
                    targets.AddRange(_myWorld.Minions);
                    break;
                case UnitType.Tree:
                    targets.AddRange(_myWorld.Trees);
                    break;
            }



            LivingUnit nearestTarget = null;

            double nearestTargetDistance = Double.MaxValue;

            var preparedList = targets;
            if (type != UnitType.Tree)
            {
                preparedList = preparedList.Where(i => i.Faction != Faction.Neutral && i.Faction != _myWizard.Faction).ToList();
            }



            foreach (var target in preparedList)
            {

                var distance = _myWizard.GetDistanceTo(target);

                if (distance < nearestTargetDistance)
                {
                    nearestTarget = target;
                    nearestTargetDistance = distance;
                }
            }

            return nearestTarget;
        }

        private List<LivingUnit> GetNearestVisibleTargets(UnitType type = UnitType.All)
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            switch (type)
            {
                case UnitType.All:
                    targets.AddRange(_myWorld.Buildings);
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    targets.AddRange(_myWorld.Minions);
                    break;
                case UnitType.Building:
                    targets.AddRange(_myWorld.Buildings);
                    break;
                case UnitType.Wizard:
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    break;
                case UnitType.Minion:
                    targets.AddRange(_myWorld.Minions);
                    break;
            }


            var result = targets.Where(i => _myWizard.GetDistanceTo(i.X, i.Y) <= _myWizard.VisionRange+_myWizard.Radius && i.Faction != Faction.Neutral && i.Faction != _myWizard.Faction).ToList();

            return result;
        }

        private List<LivingUnit> GetNearestAllyUnits(UnitType type = UnitType.All)
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            switch (type)
            {
                case UnitType.All:
                    targets.AddRange(_myWorld.Buildings);
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    targets.AddRange(_myWorld.Minions);
                    break;
                case UnitType.Building:
                    targets.AddRange(_myWorld.Buildings);
                    break;
                case UnitType.Wizard:
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    break;
                case UnitType.Minion:
                    targets.AddRange(_myWorld.Minions);
                    break;
            }


            var result = targets.Where(i => _myWizard.GetDistanceTo(i.X, i.Y) <= _myWizard.VisionRange && i.Faction != Faction.Neutral && i.Faction == _myWizard.Faction).ToList();

            return result;
        }

        private List<LivingUnit> GetNearestAttackableTargets(UnitType type = UnitType.All)
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            switch (type)
            {
                case UnitType.All:
                    targets.AddRange(_myWorld.Buildings);
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    targets.AddRange(_myWorld.Minions);
                    break;
                case UnitType.Building:
                    targets.AddRange(_myWorld.Buildings);
                    break;
                case UnitType.Wizard:
                    targets.AddRange(_myWorld.Wizards.Where(i => _myWizard.Id != i.Id));
                    break;
                case UnitType.Minion:
                    targets.AddRange(_myWorld.Minions);
                    break;
            }


            var result = targets.Where(i => _myWizard.GetDistanceTo(i.X, i.Y) <= _myWizard.CastRange && i.Faction != Faction.Neutral && i.Faction != _myWizard.Faction).ToList();

            return result;
        }

        private LivingUnit GetNearestAlly(UnitType allyType = UnitType.All)
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            if (allyType == UnitType.Minion)
            {
                targets.AddRange(_myWorld.Minions.Where(i => i.Faction == _myWizard.Faction));
            }
            else if (allyType == UnitType.Wizard)
            {
                targets.AddRange(_myWorld.Wizards.Where(i => i.Faction == _myWizard.Faction && _myWizard.Id != i.Id));
            }
            else
            {
                targets.AddRange(_myWorld.Minions.Where(i => i.Faction == _myWizard.Faction));
                targets.AddRange(_myWorld.Wizards.Where(i => i.Faction == _myWizard.Faction && _myWizard.Id != i.Id));
            }

            LivingUnit nearestTarget = null;

            var nearestTargetDistance = double.MaxValue;

            foreach (LivingUnit target in targets)
            {

                var distance = _myWizard.GetDistanceTo(target);

                if (distance < nearestTargetDistance)
                {
                    nearestTarget = target;
                    nearestTargetDistance = distance;
                }
            }

            return nearestTarget;
        }

        private LivingUnit GetNearestAllyWizard()
        {
            List<LivingUnit> targets = new List<LivingUnit>();

            targets.AddRange(_myWorld.Wizards.Where(i => i.Faction == _myWizard.Faction && _myWizard.Id != i.Id));

            LivingUnit nearestTarget = null;

            var nearestTargetDistance = double.MaxValue;

            foreach (LivingUnit target in targets)
            {

                var distance = _myWizard.GetDistanceTo(target);

                if (distance < nearestTargetDistance)
                {
                    nearestTarget = target;
                    nearestTargetDistance = distance;
                }
            }

            return nearestTarget;
        }

        /**
        * Вспомогательный класс для хранения позиций на карте.
        */

        public class Point2D
        {
            private readonly double _x;
            private readonly double _y;

            public Point2D(double x, double y)
            {
                _x = x;
                _y = y;
            }

            public double GetX()
            {
                return _x;
            }

            public double GetY()
            {
                return _y;
            }

            public double GetDistanceTo(double x, double y)
            {
                return Math.Sqrt(Math.Pow((_x - x), 2) + Math.Pow((_y - y), 2));
            }

            public double GetDistanceTo(Point2D point)
            {
                return GetDistanceTo(point.GetX(), point.GetY());
            }

            public double GetDistanceTo(Unit unit)
            {
                return GetDistanceTo(unit.X, unit.Y);
            }

            public double GetSqrDistanceTo(double x, double y)
            {
                return Math.Pow((_x - x), 2) + Math.Pow((_y - y), 2);
            }

        }



        private static LivingUnit GetNearest(Point2D point)
        {
            List<LivingUnit> targets = new List<LivingUnit>();


            targets.AddRange(_myWorld.Minions);
            targets.AddRange(_myWorld.Buildings);
            targets.AddRange(_myWorld.Trees);
            targets.AddRange(_myWorld.Wizards.Where(i => !i.IsMe));


            LivingUnit nearestTarget = null;

            var nearestTargetDistance = double.MaxValue;

            foreach (LivingUnit target in targets)
            {

                var distance = target.GetDistanceTo(point.GetX(), point.GetY());

                if (distance < nearestTargetDistance)
                {
                    nearestTarget = target;
                    nearestTargetDistance = distance;
                }
            }

            return nearestTarget;
        }


        ////
        /// 
        class MapRadar
        {

            public static int K = 4;
            public static int PointDelta = 8;
            public static double MapWidth { get; set; }
            public static double MapHeight { get; set; }
            public static double MeRadius { get; set; }
            public static double WizardViewDistance { get; set; }
            public MapRadar(double mapSize, double meRadius, Point2D me, double wizardViewDistance)
            {
                MapWidth = mapSize;
                MapHeight = mapSize;
                MeRadius = meRadius;
                WizardViewDistance = Math.Truncate(wizardViewDistance);


            }

            public class PathNode
            {

                public Point2D Position { get; set; }
                public int PathLengthFromStart { get; set; }
                public PathNode CameFrom { get; set; }
                public double HeuristicEstimatePathLength { get; set; }
                public double EstimateFullPathLength
                {
                    get
                    {
                        return this.PathLengthFromStart + this.HeuristicEstimatePathLength;
                    }
                }
            }

            private static void FillCircle(Graphics gr, Point2D point, double r, Color color)
            {
                var brush = new SolidBrush(color);
                var pen = new Pen(color);

                var x = Convert.ToInt32(point.GetX() - r);
                var y = Convert.ToInt32(point.GetY() - r);
                gr.FillEllipse(brush, x, y, Convert.ToInt32(r * 2), Convert.ToInt32(r * 2));

                x = Convert.ToInt32(point.GetX() - r - _myWizard.Radius);
                y = Convert.ToInt32(point.GetY() - r - _myWizard.Radius);
                gr.DrawEllipse(pen, x, y, Convert.ToInt32((r + _myWizard.Radius) * 2), Convert.ToInt32((r + _myWizard.Radius) * 2));
            }

            public static void SaveToFile(Collection<PathNode> closedSet, List<Point2D> path, Point2D start, Point2D goal)
            {
                var xDimension = Convert.ToInt32(MapWidth);
                var yDimension = Convert.ToInt32(MapHeight);

                var bmp = new Bitmap(xDimension, yDimension);

                var filename = "map-" + _myGame.TickCount + ".bmp";

                Graphics gr = Graphics.FromImage(bmp);

                var brush = new SolidBrush(Color.Brown);
                var pen = new Pen(Color.Brown);
                var me = _myWorld.Wizards.FirstOrDefault(i => i.IsMe);
                if (me != null)
                {
                    FillCircle(gr, new Point2D(me.X, me.Y), me.Radius, Color.Brown);
                    //gr.FillEllipse(brush, Convert.ToInt32(me.X), Convert.ToInt32(me.Y), Convert.ToInt32(me.Radius), Convert.ToInt32(me.Radius));
                }

                var allyWizards = _myWorld.Wizards.Where(i => !i.IsMe && i.Faction == _myWizard.Faction);
                if (allyWizards.Any())
                {
                    foreach (var allyWizard in allyWizards)
                    {
                        brush = new SolidBrush(Color.BlueViolet);

                        //gr.FillEllipse(brush, Convert.ToInt32(allyWizard.X), Convert.ToInt32(allyWizard.Y), Convert.ToInt32(allyWizard.Radius), Convert.ToInt32(allyWizard.Radius));

                        FillCircle(gr, new Point2D(allyWizard.X, allyWizard.Y), allyWizard.Radius, Color.BlueViolet);
                    }
                }

                var enemyWizards = _myWorld.Wizards.Where(i => !i.IsMe && i.Faction != _myWizard.Faction);
                if (enemyWizards.Any())
                {
                    foreach (var enemyWizard in enemyWizards)
                    {
                        brush = new SolidBrush(Color.Cornsilk);
                        //gr.FillEllipse(brush, Convert.ToInt32(enemyWizard.X), Convert.ToInt32(enemyWizard.Y), Convert.ToInt32(enemyWizard.Radius), Convert.ToInt32(enemyWizard.Radius));
                        FillCircle(gr, new Point2D(enemyWizard.X, enemyWizard.Y), enemyWizard.Radius, Color.Cornsilk);
                    }
                }

                var allyBuildings = _myWorld.Buildings.Where(i => i.Faction == _myWizard.Faction);
                if (allyBuildings.Any())
                {
                    foreach (var allyBuilding in allyBuildings)
                    {
                        brush = new SolidBrush(Color.WhiteSmoke);
                        //gr.FillEllipse(brush, Convert.ToInt32(allyBuilding.X), Convert.ToInt32(allyBuilding.Y), Convert.ToInt32(allyBuilding.Radius), Convert.ToInt32(allyBuilding.Radius));
                        FillCircle(gr, new Point2D(allyBuilding.X, allyBuilding.Y), allyBuilding.Radius, Color.WhiteSmoke);
                    }
                }

                var enemyBuildings = _myWorld.Buildings.Where(i => i.Faction != _myWizard.Faction);
                if (enemyBuildings.Any())
                {
                    foreach (var enemyBuilding in enemyBuildings)
                    {
                        brush = new SolidBrush(Color.CadetBlue);
                        //gr.FillEllipse(brush, Convert.ToInt32(enemyBuilding.X), Convert.ToInt32(enemyBuilding.Y), Convert.ToInt32(enemyBuilding.Radius), Convert.ToInt32(enemyBuilding.Radius));
                        FillCircle(gr, new Point2D(enemyBuilding.X, enemyBuilding.Y), enemyBuilding.Radius, Color.CadetBlue);
                    }
                }

                var trees = _myWorld.Trees;
                if (trees.Any())
                {
                    foreach (var tree in trees)
                    {
                        brush = new SolidBrush(Color.DarkSeaGreen);
                        //gr.FillEllipse(brush, Convert.ToInt32(tree.X), Convert.ToInt32(tree.Y), Convert.ToInt32(tree.Radius), Convert.ToInt32(tree.Radius));
                        FillCircle(gr, new Point2D(tree.X, tree.Y), tree.Radius, Color.DarkSeaGreen);
                    }
                }

                var minions = _myWorld.Minions;
                if (minions.Any())
                {
                    foreach (var minion in minions)
                    {
                        brush = new SolidBrush(Color.WhiteSmoke);
                        //gr.FillEllipse(brush, Convert.ToInt32(tree.X), Convert.ToInt32(tree.Y), Convert.ToInt32(tree.Radius), Convert.ToInt32(tree.Radius));
                        FillCircle(gr, new Point2D(minion.X, minion.Y), minion.Radius, Color.WhiteSmoke);
                    }
                }


                foreach (var d in closedSet)
                {
                    brush = new SolidBrush(Color.MistyRose);
                    gr.FillRectangle(brush, Convert.ToInt32(d.Position.GetX()), Convert.ToInt32(d.Position.GetY()), 1, 1);
                }

                foreach (var d in path)
                {
                    brush = new SolidBrush(Color.Yellow);
                    gr.FillRectangle(brush, Convert.ToInt32(d.GetX()), Convert.ToInt32(d.GetY()), 1, 1);
                }

                brush = new SolidBrush(Color.Cyan);
                gr.FillRectangle(brush, Convert.ToInt32(start.GetX()), Convert.ToInt32(start.GetY()), 1, 1);

                brush = new SolidBrush(Color.DarkOrange);
                gr.FillRectangle(brush, Convert.ToInt32(goal.GetX()), Convert.ToInt32(goal.GetY()), 1, 1);
                gr.DrawEllipse(new Pen(Color.DarkOrange), Convert.ToInt32(goal.GetX() - 20), Convert.ToInt32(goal.GetY() - 20), 40, 40);


                bmp.Save(filename, System.Drawing.Imaging.ImageFormat.Bmp);
            }


            public List<Point2D> ClosedNodes;
            public static List<Point2D> FindPath(Point2D start, Point2D goal)
            {

                // Шаг 1.
                var closedSet = new Collection<PathNode>();
                var openSet = new Collection<PathNode>();
                // Шаг 2.
                PathNode startNode = new PathNode()
                {
                    Position = start,
                    CameFrom = null,
                    PathLengthFromStart = 0,
                    HeuristicEstimatePathLength = GetHeuristicPathLength(start, goal)
                };
                openSet.Add(startNode);

                var lastCurrentMode = new PathNode();


                double additionalDelta = 0;

                var props = new List<LivingUnit>();
                props.AddRange(_myWorld.Trees);
                props.AddRange(_myWorld.Buildings);
                props.AddRange(_myWorld.Minions);
                props.AddRange(_myWorld.Wizards.Where(i => !i.IsMe));

                foreach (var livingUnit in props)
                {
                    if (
                        Math.Pow(livingUnit.X - goal.GetX(), 2) + Math.Pow(livingUnit.Y - goal.GetY(), 2) <=
                        Math.Pow(livingUnit.Radius + _myWizard.Radius+ K, 2)
                    )
                    {
                        additionalDelta = livingUnit.Radius + _myWizard.Radius+K;
                        break;
                    }
                }

                while (openSet.Count > 0)
                {



                    // Шаг 3.

                    //refactored?
                    //var currentNode = openSet.OrderBy(node =>
                    // node.EstimateFullPathLength).First();

                    var currentNode = openSet[0];
                    var minEstimatedFullPathLength = openSet[0].EstimateFullPathLength;
                    for (int i = 1; i < openSet.Count; i++)
                    {
                        if (openSet[i].EstimateFullPathLength < minEstimatedFullPathLength)
                        {
                            minEstimatedFullPathLength = openSet[i].EstimateFullPathLength;
                            currentNode = openSet[i];
                        }
                    }

                    lastCurrentMode = currentNode;

                    if (closedSet.Count >= 4000)
                    {
                        //Console.WriteLine("!!!!!!!!!!!!!!!!!!!!!ERRRROOOOORR!!!");

                        var closestNodeToGoal = closedSet.OrderBy(i => i.Position.GetDistanceTo(goal)).FirstOrDefault();
                        var path = GetPathForNode(closestNodeToGoal);

                        //SaveToFile(closedSet, path, start, goal);

                        return path;
                    }

                    // Шаг 4.

                    if (Math.Abs(currentNode.Position.GetX() - goal.GetX()) <= PointDelta + 1 + additionalDelta
                         && Math.Abs(currentNode.Position.GetY() - goal.GetY()) <= PointDelta + 1 + additionalDelta)
                    {

                        var path = GetPathForNode(currentNode);

                        //SaveToFile(openSet, path, start, goal);

                        return path;
                    }




                    //if (unitPoint.GetSqrDistanceTo(goal.GetX(), goal.GetY()) <= Math.Pow(_myWizard.Radius + unit.Radius + 1 + 3*K, 2))
                    //{
                    //    //Console.WriteLine("Error");
                    //    return GetPathForNode(currentNode);
                    //}

                    // Шаг 5.
                    openSet.Remove(currentNode);
                    closedSet.Add(currentNode);


                    // Шаг 6.

                    var neighbours = GetNeighbours(currentNode, goal, closedSet);
                    foreach (var neighbourNode in neighbours)
                    {



                        // Шаг 7.

                        //var shouldStop = false;
                        //for (var i = 0; i < closedSet.Count; i++)
                        //{
                        //    if (Math.Abs(closedSet[i].Position.GetX() - neighbourNode.Position.GetX()) < 0.5 &&
                        //        Math.Abs(closedSet[i].Position.GetY() - neighbourNode.Position.GetY()) < 0.5)
                        //    {
                        //        shouldStop = true;
                        //    }
                        //}
                        //if (shouldStop)
                        //{
                        //    continue;
                        //}

                        //refactored?
                        //if (closedSet.Any(node => Math.Abs(node.Position.GetX() - neighbourNode.Position.GetX()) < 0.5 && Math.Abs(node.Position.GetY() - neighbourNode.Position.GetY()) < 0.5))
                        //    continue;


                        var openNode = (PathNode)null;
                        foreach (var node in openSet)
                        {
                            if (Math.Abs(node.Position.GetX() - neighbourNode.Position.GetX()) < 0.5 && Math.Abs(node.Position.GetY() - neighbourNode.Position.GetY()) < 0.5)
                            {
                                openNode = node;
                                break;
                            }
                        }

                        //var openNode = openSet.FirstOrDefault(node =>
                        //  node.Position == neighbourNode.Position);
                        // Шаг 8.
                        if (openNode == null)
                            openSet.Add(neighbourNode);
                        else
                            if (openNode.PathLengthFromStart > neighbourNode.PathLengthFromStart)
                        {
                            // Шаг 9.
                            openNode.CameFrom = currentNode;
                            openNode.PathLengthFromStart = neighbourNode.PathLengthFromStart;
                        }
                    }
                }
                // Шаг 10.

                var unreachedPath = GetPathForNode(lastCurrentMode);
                //SaveToFile(closedSet, unreachedPath, start, goal);
                return unreachedPath;
            }

            private static int GetDistanceBetweenNeighbours()
            {
                return K;
            }

            private static double GetHeuristicPathLength(Point2D from, Point2D to)
            {
                //return Math.Pow(from.GetX() - to.GetX(), 2) + Math.Pow(from.GetY() - to.GetY(), 2);
                return Math.Abs(from.GetX() - to.GetX()) + Math.Abs(from.GetY() - to.GetY());
            }

            private static Collection<PathNode> GetNeighbours(PathNode pathNode,
  Point2D goal, Collection<PathNode> closedSet)
            {
                var result = new Collection<PathNode>();

                // Соседними точками являются соседние по стороне клетки.
                var neighbourPoints = new Point2D[8];
                neighbourPoints[0] = new Point2D(pathNode.Position.GetX() + PointDelta, pathNode.Position.GetY());
                neighbourPoints[1] = new Point2D(pathNode.Position.GetX() - PointDelta, pathNode.Position.GetY());
                neighbourPoints[2] = new Point2D(pathNode.Position.GetX(), pathNode.Position.GetY() + PointDelta);
                neighbourPoints[3] = new Point2D(pathNode.Position.GetX(), pathNode.Position.GetY() - PointDelta);

                neighbourPoints[4] = new Point2D(pathNode.Position.GetX() + PointDelta, pathNode.Position.GetY() + PointDelta);
                neighbourPoints[5] = new Point2D(pathNode.Position.GetX() + PointDelta, pathNode.Position.GetY() - PointDelta);
                neighbourPoints[6] = new Point2D(pathNode.Position.GetX() - PointDelta, pathNode.Position.GetY() + PointDelta);
                neighbourPoints[7] = new Point2D(pathNode.Position.GetX() - PointDelta, pathNode.Position.GetY() - PointDelta);

                foreach (var point in neighbourPoints)
                {

                    var isCurrentPointInClosedSet = false;
                    foreach (var node in closedSet)
                    {
                        if (Math.Abs(node.Position.GetX() - point.GetX()) <= 0 && Math.Abs(node.Position.GetY() - point.GetY()) <= 0)
                        {
                            isCurrentPointInClosedSet = true;
                            break;
                        }

                    }
                    if (isCurrentPointInClosedSet)
                    {
                        continue;
                    }

                    // Проверяем, что не вышли за границы карты.
                    if (point.GetX() <= _myWizard.Radius || point.GetX() >= MapWidth - 1 - _myWizard.Radius)
                        continue;
                    if (point.GetY() <= _myWizard.Radius || point.GetY() >= MapHeight + 1 - _myWizard.Radius)
                        continue;
                    // Проверяем, что по клетке можно ходить.


                    var targets = new List<LivingUnit>();

                    //разрешаем ходить через деревья при условии их уничтожения
                    targets.AddRange(_myWorld.Trees.Where(i=>i.Life >=_myGame.MagicMissileDirectDamage));

                    targets.AddRange(_myWorld.Buildings);
                    targets.AddRange(_myWorld.Minions);
                    targets.AddRange(_myWorld.Wizards.Where(i => !i.IsMe));

                    var shouldStop = false;
                    foreach (var livingUnit in targets)
                    {
                        if (
                            Math.Pow(livingUnit.X - point.GetX(), 2) + Math.Pow(livingUnit.Y - point.GetY(), 2) <=
                            Math.Pow(_myWizard.Radius + livingUnit.Radius + K, 2)
                        )
                        {
                            shouldStop = true;
                        }
                       

                    }
                    if (shouldStop)
                    {
                        continue;
                    }
                  

                    // Заполняем данные для точки маршрута.
                    var neighbourNode = new PathNode()
                    {
                        Position = point,
                        CameFrom = pathNode,
                        PathLengthFromStart = pathNode.PathLengthFromStart +
                        GetDistanceBetweenNeighbours(),
                        HeuristicEstimatePathLength = GetHeuristicPathLength(point, goal)
                    };
                    result.Add(neighbourNode);
                }
                return result;
            }

            

            static bool commonSectionCircle(double x1, double y1, double x2, double y2,
                                 double xC, double yC, double R)
            {
                x1 -= xC;
                y1 -= yC;
                x2 -= xC;
                y2 -= yC;

                double dx = x2 - x1;
                double dy = y2 - y1;

                //составляем коэффициенты квадратного уравнения на пересечение прямой и окружности.
                //если на отрезке [0..1] есть отрицательные значения, значит отрезок пересекает окружность
                double a = dx * dx + dy * dy;
                double b = 2 * (x1 * dx + y1 * dy);
                double c = x1 * x1 + y1 * y1 - R * R;

                //а теперь проверяем, есть ли на отрезке [0..1] решения
                if (-b < 0)
                    return (c < 0);
                if (-b < (2 * a))
                    return ((4 * a * c - b * b) < 0);

                return (a + b + c < 0);
            }

            private static List<Point2D> GetPathForNode(PathNode pathNode)
            {
                var result = new List<Point2D>();
                var currentNode = pathNode;

                var trees = _myWorld.Trees;
                treeListToDestroy = new List<Tree>();

                while (currentNode != null)
                {

                    //если путь лежит через дерево, то уничтожаем его
                   
                    foreach (var tree in trees)
                    {
                        if (tree.GetDistanceTo(currentNode.Position.GetX(), currentNode.Position.GetY()) <=
                            tree.Radius + _myWizard.Radius + K)
                        {
                            treeListToDestroy.Add(tree);
                        }
                    }

                    result.Add(new Point2D(currentNode.Position.GetX(), currentNode.Position.GetY()));
                    currentNode = currentNode.CameFrom;
                }
                result.Reverse();

                if (result.Count > 0)
                {
                    result.RemoveAt(0);
                }

                treeListToDestroy = treeListToDestroy.Distinct().ToList();
                return result;
            }


        }

        static bool IsLineIntercectCircle(double x1, double y1, double x2, double y2,
                double xC, double yC, double R)
        {
            var a = Math.Pow(x2 - x1, 2) + Math.Pow(y2 - y1, 2);
            var b = 2 * ((x2 - x1) * (x1 - xC) + (y2 - y1) * (y1 - yC));
            var c = Math.Pow(xC, 2) + Math.Pow(yC, 2) + Math.Pow(x1, 2) + Math.Pow(y1, 2) - 2 * (xC * x1 + yC * y1) - Math.Pow(R, 2);
            var i = Math.Pow(b, 2) - 4 * a * c;

            // no intersection
            if (i < 0.0)
            {
                return false;
            }
            // intersect's
            if (i >= 0.0)
            {
                return true;
            }

            return false;
        }

        public int GetProgressByLane(LaneType laneType)
        {
            var points = GetWaypointsByLaneType(laneType);
            if (points.Any())
            {

                var ourForces = new List<LivingUnit>();
                ourForces.AddRange(_myWorld.Wizards.Where(i=>i.Faction==_myWizard.Faction));
               // ourForces.AddRange(_myWorld.Minions.Where(i => i.Faction == _myWizard.Faction));

                var maxCount = points.Length;
                var progressCount = 0;
                for (var ind =maxCount-1; ind>=0; ind--)
                {
                    var currentPoint = points[ind];
                    if (
                        ourForces.Any(
                            i => i.GetDistanceTo(currentPoint.GetX(), currentPoint.GetY()) <= _myWizard.VisionRange))
                    {
                        progressCount = ind;
                        break;
                    }
                }

                decimal progressPercent = (decimal)progressCount/maxCount*100;
                return Convert.ToInt32(Math.Floor(progressPercent));
            }

            return 0;
        }

        public Point2D GetLaneSwitchPoint(LaneType laneType)
        {
            var points = GetWaypointsByLaneType(laneType);
            if (points.Any())
            {

                var ourForces = new List<LivingUnit>();
                ourForces.AddRange(_myWorld.Wizards.Where(i => i.Faction == _myWizard.Faction));
                //ourForces.AddRange(_myWorld.Minions.Where(i => i.Faction == _myWizard.Faction));

                var maxCount = points.Length;
                var progressCount = 0;
                for (var ind = maxCount - 1; ind >= 0; ind--)
                {
                    var currentPoint = points[ind];
                    if (
                        ourForces.Any(
                            i => i.GetDistanceTo(currentPoint.GetX(), currentPoint.GetY()) <= _myWizard.VisionRange))
                    {
                        progressCount = ind;
                        break;
                    }
                }

                if (progressCount < 0)
                {
                    progressCount = 0;
                }

                var result = points[progressCount];
                return result;
            }

            return null;
        }

        public bool TrySwitchLine()
        {
            var laneTopProgress = GetProgressByLane(LaneType.Top);
            var laneMiddleProgress = GetProgressByLane(LaneType.Middle);
            var laneBottomProgress = GetProgressByLane(LaneType.Bottom);

            var myProgress = 0;

            if (lane == LaneType.Top)
            {
                myProgress = laneTopProgress;
                if (myProgress >= 50 && laneMiddleProgress < 25)
                {
                    //swith to mid
                    SwitchLine(LaneType.Middle);
                    return true;
                }
                if (myProgress >= 50 && laneBottomProgress <= 20)
                {
                    //swith to bottom
                    SwitchLine(LaneType.Bottom);
                    return true;
                }
            }
            if (lane == LaneType.Middle)
            {
                myProgress = laneMiddleProgress;
                if (myProgress >= 50 && laneTopProgress <= 30)
                {
                    //swith to top
                    SwitchLine(LaneType.Top);
                    return true;
                }
                if (myProgress >= 50 && laneBottomProgress <= 20)
                {
                    //swith to bottom
                    SwitchLine(LaneType.Bottom);
                    return true;
                }
            }
            if (lane == LaneType.Bottom)
            {
                myProgress = laneBottomProgress;
                if (myProgress >= 50 && laneTopProgress <= 20)
                {
                    //swith to top
                    SwitchLine(LaneType.Top);
                    return true;
                }
                if (myProgress >= 50 && laneMiddleProgress < 25)
                {
                    //swith to middle
                    SwitchLine(LaneType.Middle);
                    return true;
                }
            }

            return false;
        }

        public void SwitchLine(LaneType laneType)
        {
            lane = laneType;
            waypoints = GetWaypointsByLaneType(laneType);
            return;
        }

        public void LearnSkill(int level)
        {
            switch (level)
            {


                //

                case 1:
                    _myMove.SkillToLearn = SkillType.RangeBonusPassive1;
                    break;
                case 2:
                    _myMove.SkillToLearn = SkillType.RangeBonusAura1;
                    break;
                case 3:
                    _myMove.SkillToLearn = SkillType.RangeBonusPassive2;
                    break;
                case 4:
                    _myMove.SkillToLearn = SkillType.RangeBonusAura2;
                    break;
                case 5:
                    _myMove.SkillToLearn = SkillType.AdvancedMagicMissile;
                    break;

                    //

                case 6:
                    _myMove.SkillToLearn = SkillType.MagicalDamageBonusPassive1;
                    break;
                case 7:
                    _myMove.SkillToLearn = SkillType.MagicalDamageBonusAura1;
                    break;
                case 8:
                    _myMove.SkillToLearn = SkillType.MagicalDamageBonusPassive2;
                    break;
                case 9:
                    _myMove.SkillToLearn = SkillType.MagicalDamageBonusAura2;
                    break;
                case 10:
                    _myMove.SkillToLearn = SkillType.FrostBolt;
                    break;

           



                // 

                case 11:
                    _myMove.SkillToLearn = SkillType.MovementBonusFactorPassive1;
                    break;
                case 12:
                    _myMove.SkillToLearn = SkillType.MovementBonusFactorAura1;
                    break;
                case 13:
                    _myMove.SkillToLearn = SkillType.MovementBonusFactorPassive2;
                    break;
                case 14:
                    _myMove.SkillToLearn = SkillType.MovementBonusFactorAura2;
                    break;
                case 15:
                    _myMove.SkillToLearn = SkillType.Haste;
                    break;

                //


                case 16:
                    _myMove.SkillToLearn = SkillType.MagicalDamageAbsorptionPassive1;
                    break;
                case 17:
                    _myMove.SkillToLearn = SkillType.MagicalDamageAbsorptionAura1;
                    break;
                case 18:
                    _myMove.SkillToLearn = SkillType.MagicalDamageAbsorptionPassive2;
                    break;
                case 19:
                    _myMove.SkillToLearn = SkillType.MagicalDamageAbsorptionAura2;
                    break;
                case 20:
                    _myMove.SkillToLearn = SkillType.Shield;
                    break;

                //

                case 21:
                    _myMove.SkillToLearn = SkillType.StaffDamageBonusPassive1;
                    break;
                case 22:
                    _myMove.SkillToLearn = SkillType.StaffDamageBonusAura1;
                    break;
                case 23:
                    _myMove.SkillToLearn = SkillType.StaffDamageBonusPassive2;
                    break;
                case 24:
                    _myMove.SkillToLearn = SkillType.StaffDamageBonusAura2;
                    break;
                case 25:
                    _myMove.SkillToLearn = SkillType.Fireball;
                    break;
                   

            }
        }


    }
}